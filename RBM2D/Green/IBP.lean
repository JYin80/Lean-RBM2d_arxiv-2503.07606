/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Green.FlucAvg
import RBM2D.Green.GreenDeriv
import RBM2D.Green.IBPPoly

/-!
# The Gaussian integration-by-parts display, as an identity

The model is that of `RBM2D/Gauss/Model.lean`.  The paper (arXiv:2503.07606) does not state this
file as a lemma: it says that the estimates on `G_t` "follow that of Lemma 4.2 in [YY_25], which
is dimension-independent" (Section "Estimates for entries of `G`"), and the fluctuation
averaging and the integration-by-parts display behind (`GavLGEX`) are proved internally.  The
display is

  `E_i(G_ii - m) = E_i[m(-H - tm)G]_ii = t m Σ_k S_ik E_i[G_ii (G_kk - m)]`,

an **identity** (no `≺`, no error term); the remainder `ibpRem` is what separates it from the
paper's `t m² Σ_k S_ik (G_kk - m) + O≺(Ψ²)`.

The four steps:

1. **Algebra.**  `G - m = m(-H - tm)G` (`green_sub_smul_one_eq`, private), from `m(t m + z_t) = -1`.
2. **Gaussian integration by parts.**  The coordinate derivative of the resolvent along `Hflow`
   (`hasDerivAt_*`), the tameness of the entries (`tame_*`), Stein's identity for one resolvent
   entry (`integral_coord_mul_*`), the collapse of the coordinate sum to a row of the variance
   profile (`sum_gvar_Bmat_sandwich_diag`), and the same inside `E_k` (`condRow_*`,
   `condRow_Hflow_mul_green_diag`).
3. **The display** `condExpDiag_eq_sum_Sblk`.
4. **The remainder** `ibpRem`, `ibpRem_eq_add`.

## Notation

* The objects are `Sizes`, `Sizes.SeqΩ d`, `Sizes.SeqCoord d`, `Sizes.seqP d`,
  `Sizes.seqGvar d c`, `Sizes.seqHflow d n u`; the coordinates `p : Coord L W` and
  `usedCoords L W` (`L = d.L n`, `W = d.W n`) are reached on the common space through
  `crd d n p` (`RBM2D/Green/GreenDeriv.lean`).  Statements about the matrix `Bmat` alone are
  stated over `Idx L W`.
* `‖G‖ ≤ η_t⁻¹` is `norm_green_apply_le_etaT`; `sub_mul_green_of_im`, `mE_mul_add_zt`,
  `sub_smul_one_apply`, `IsRowCoord`, `rowSplit`, `condRow`, `condExpDiag` are those of the
  other files; nothing of these is redefined.
* **d = 2 change.**  The variance profile of the block model becomes `svar` on the fine index
  `Idx L W = Z2 (W L)`.  The row sum `Σ_k svar(i,k) = 1` (`IBP_sum_svar_row`) needs `3 ≤ L`
  (five distinct residues of `sbSupport L`); the five-block variance is `svar ≤ (5 W²)⁻¹`.
  The block profile `Sblk2` enters only through `Sblk2_eq_svar`, which this file does not need.
* `Bmat_swap_true`, `Bmat_swap_false`, `IBP_gvar_eq` and `IBP_sum_used_eq_sum_pairs` (with its three
  helpers) are private `IBP_*` helpers (the bookkeeping of the used coordinates).
* Public names: `IBP_sum_svar_row` and the statements of the display; every other helper is
  private.

`hG : GaussIBP d` is a hypothesis of every statement that integrates; it is the theorem
`gaussIBP d` (`RBM2D/Green/IBPPoly.lean`).
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss
open scoped Matrix.Norms.L2Operator NNReal

/-! ### Step 1: the algebraic identity `G - m = m(-H - tm)G`

Everything here is deterministic. -/

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The identity `G - m = m(-H - tm)G`**, from the self-consistent equation
`m = -(t m + z_t)⁻¹` (`mE_mul_add_zt`).  Taking the `ii` entry and applying `E_i` is the first
step of the integration-by-parts display. -/
private theorem green_sub_smul_one_eq {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {E t : ℝ}
    (hE : |E| ≤ 2) (hz : (spectralZ E t).im ≠ 0) :
    green H (spectralZ E t) - spectralM E • (1 : Matrix ι ι ℂ)
      = spectralM E • ((-H - ((t : ℂ) * spectralM E) • (1 : Matrix ι ι ℂ))
          * green H (spectralZ E t)) := by
  have hGH : (H - (spectralZ E t) • (1 : Matrix ι ι ℂ)) * green H (spectralZ E t) = 1 :=
    sub_mul_green_of_im hH hz
  have hkey : spectralM E * ((t : ℂ) * spectralM E + spectralZ E t) = -1 :=
    mE_mul_add_zt hE t
  have hsplit : (-H - ((t : ℂ) * spectralM E) • (1 : Matrix ι ι ℂ))
      = -(H - (spectralZ E t) • (1 : Matrix ι ι ℂ))
        - (((t : ℂ) * spectralM E + spectralZ E t) • (1 : Matrix ι ι ℂ)) := by
    rw [add_smul]
    abel
  rw [hsplit, sub_mul, neg_mul, hGH, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_neg,
    smul_smul, hkey, neg_smul, one_smul]
  abel

end Algebra

/-! ### Step 2a: moving one Gaussian coordinate

Stein's identity replaces `ω_c` by `gvar_c · ∂_c`, so the display needs the derivative of a
resolvent entry along a single Gaussian coordinate.  The lemmas below are pathwise: no
integration yet. -/

section Deriv

/-- **Moving the Gaussian coordinate `p` moves `H_u` along `√u · B_p`**. -/
theorem hasDerivAt_Hflow_update (d : Sizes) (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ d)
    {p : Coord (d.L n) (d.W n)} (hp : p ∈ usedCoords (d.L n) (d.W n)) :
    HasDerivAt (fun t : ℝ => Sizes.seqHflow d n u (Function.update ω (crd d n p) t))
      (Real.sqrt u • Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2) (ω (crd d n p)) := by
  set c := crd d n p with hc
  set B := Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2 with hB
  have hline : ∀ t : ℝ, Sizes.seqHflow d n u (Function.update ω c t)
      = Sizes.seqHflow d n u ω + (Real.sqrt u * (t - ω c)) • B := by
    intro t
    rw [GreenDeriv_seqHflow_eq_realSmul, GreenDeriv_seqHflow_eq_realSmul,
      GreenDeriv_seqXmat_update d n ω hp t, smul_add, smul_smul]
  have hscal : HasDerivAt (fun t : ℝ => Real.sqrt u * (t - ω c)) (Real.sqrt u) (ω c) := by
    simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul (Real.sqrt u)
  have h1 : HasDerivAt (fun t : ℝ => Sizes.seqHflow d n u ω + (Real.sqrt u * (t - ω c)) • B)
      (Real.sqrt u • B) (ω c) := (hscal.smul_const B).const_add _
  exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hline t)

/-- **The coordinate derivative of the resolvent**: `∂_c G_u = -√u · G_u B_c G_u`.  The derivative
of a resolvent is again a product of
resolvents, which is why the global bound `‖G‖ ≤ η⁻¹` makes every Stein hypothesis free. -/
theorem hasDerivAt_green_Hflow_update (d : Sizes) (n : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (ω : Sizes.SeqΩ d) {p : Coord (d.L n) (d.W n)} (hp : p ∈ usedCoords (d.L n) (d.W n)) :
    HasDerivAt
      (fun t : ℝ => green (Sizes.seqHflow d n u (Function.update ω (crd d n p) t)) z)
      (-(Real.sqrt u) • (green (Sizes.seqHflow d n u ω) z
        * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2 * green (Sizes.seqHflow d n u ω) z))
      (ω (crd d n p)) := by
  set c := crd d n p with hc
  set B := Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2 with hB
  set G := green (Sizes.seqHflow d n u ω) z with hG
  have hBherm : B.IsHermitian := GreenDeriv_Bmat_isHermitian hp
  have hres : ∀ t : ℝ, resH z (Sizes.seqHflow d n u (Function.update ω c t))
      = green (Sizes.seqHflow d n u (Function.update ω c t)) z :=
    fun t => GreenDeriv_resH_of_isHermitian (Sizes.seqHflow_isHermitian d n u _)
  have hMG : resH z (Sizes.seqHflow d n u ω) = G :=
    GreenDeriv_resH_of_isHermitian (Sizes.seqHflow_isHermitian d n u ω)
  have hpath := hasDerivAt_Hflow_update d n u ω hp
  have hself : Sizes.seqHflow d n u (Function.update ω c (ω c)) = Sizes.seqHflow d n u ω := by
    rw [Function.update_eq_self]
  have key := (hasFDerivAt_resH hz
    (Sizes.seqHflow d n u (Function.update ω c (ω c)))).comp_hasDerivAt (ω c) hpath
  rw [hself] at key
  have hval : (-((ContinuousLinearMap.mulLeftRight ℝ
      (Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ)
      (resH z (Sizes.seqHflow d n u ω)) (resH z (Sizes.seqHflow d n u ω))).comp
        (hermCLM (Idx (d.L n) (d.W n))))) (Real.sqrt u • B) = -(Real.sqrt u) • (G * B * G) := by
    simp only [_root_.neg_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, map_smul, GreenDeriv_hermCLM_of_isHermitian hBherm,
      ContinuousLinearMap.mulLeftRight_apply, hMG]
    rw [smul_neg, neg_smul]
  rw [hval] at key
  exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hres t).symm)

end Deriv

/-! ### Step 2b: the sandwich collapses to two entries

`B_p` has at most two nonzero entries, so `G B_p G` is a sum of two products of resolvent
entries.  This is the Lean form of the paper's `∂_{H_ij}(G_s)_{xy} = -(G_s)_{xi}(G_s)_{jy}`
(proof of `clt-lemma`).  The lemmas are matrix algebra on
`Bmat L W`. -/

section Sandwich

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Off the diagonal, `M B_{ij,b} M'` has exactly two terms. -/
private theorem mul_Bmat_mul_apply_of_ne {M M' : Matrix (Idx L W) (Idx L W) ℂ} {i j : Idx L W}
    (hij : i ≠ j) (b : Bool) (a c : Idx L W) :
    (M * Bmat L W i j b * M') a c
      = (if b then (1 : ℂ) else Complex.I) * (M a i * M' j c)
        + (if b then (1 : ℂ) else -Complex.I) * (M a j * M' i c) := by
  have hrow : ∀ l : Idx L W, (M * Bmat L W i j b) a l
      = (if l = j then (if b then (1 : ℂ) else Complex.I) * M a i else 0)
        + (if l = i then (if b then (1 : ℂ) else -Complex.I) * M a j else 0) := by
    intro l
    rw [Matrix.mul_apply]
    by_cases hlj : l = j
    · have hli : ¬ l = i := fun h => hij (h ▸ hlj)
      rw [ite_eq_left hlj, ite_eq_right hli, add_zero]
      refine (Finset.sum_eq_single i ?_ ?_).trans ?_
      · intro k _ hk
        rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hk h.1),
          ite_eq_right (fun h => hli h.2), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
      · rw [GreenDeriv_Bmat_apply, ite_eq_left ⟨rfl, hlj⟩, mul_comm]
    · by_cases hli : l = i
      · rw [ite_eq_right hlj, ite_eq_left hli, zero_add]
        refine (Finset.sum_eq_single j ?_ ?_).trans ?_
        · intro k _ hk
          rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hlj h.2),
            ite_eq_right (fun h => hk h.1), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ j) h
        · rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hlj h.2), ite_eq_left ⟨rfl, hli⟩,
            mul_comm]
      · rw [ite_eq_right hlj, ite_eq_right hli, add_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hlj h.2), ite_eq_right (fun h => hli h.2),
          mul_zero]
  rw [Matrix.mul_apply]
  simp only [hrow, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_eq' Finset.univ i,
    ite_eq_left (Finset.mem_univ j), ite_eq_left (Finset.mem_univ i)]
  ring_nf

/-- On the diagonal the real tag gives a single entry.  (`(i, i, false)` is never a used
coordinate, so the imaginary tag does not occur there.) -/
private theorem mul_Bmat_mul_apply_diag {M M' : Matrix (Idx L W) (Idx L W) ℂ} (i a c : Idx L W) :
    (M * Bmat L W i i true * M') a c = M a i * M' i c := by
  have hrow : ∀ l : Idx L W, (M * Bmat L W i i true) a l = (if l = i then M a i else 0) := by
    intro l
    rw [Matrix.mul_apply]
    by_cases hli : l = i
    · rw [ite_eq_left hli]
      refine (Finset.sum_eq_single i ?_ ?_).trans ?_
      · intro k _ hk
        rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hk h.1),
          ite_eq_right (fun h => hk h.1), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
      · rw [GreenDeriv_Bmat_apply, ite_eq_left ⟨rfl, hli⟩]
        simp
    · refine (Finset.sum_eq_zero fun k _ => ?_).trans (ite_eq_right hli).symm
      rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hli h.2), ite_eq_right (fun h => hli h.2),
        mul_zero]
  rw [Matrix.mul_apply]
  simp only [hrow, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ i)]

end Sandwich

/-! ### Step 2c: resolvent entries are tame

`RBM.Green.gaussIBP` is Stein's identity for *polynomially bounded* test functions
(`RBM.Green.Tame`), which is the version the display needs: its integrand carries a factor
`H_ik`, so it is never globally bounded.  Resolvent entries themselves are tame for the cheapest
possible reason: the deterministic envelope `‖G‖ ≤ η_t⁻¹` (`norm_green_apply_le_etaT`). -/

section Tame

variable {d : Sizes} {n : ℕ} {E t : ℝ}

/-- `Im z_t ≠ 0` strictly inside the flow. -/
private theorem zt_im_ne_zero_of_lt_one (hE : |E| < 2) (ht : t < 1) :
    (spectralZ E t).im ≠ 0 := by
  rw [spectralZ_im]
  exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'

/-- **Every resolvent entry is tame**.  No polynomial is
needed: the entry is bounded by `η_t⁻¹` on the whole space, so the dominating polynomial can be
taken constant. -/
theorem tame_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ) (a b : Idx (d.L n) (d.W n)) :
    Tame d (fun ω : Sizes.SeqΩ d => green (Sizes.seqHflow d n u ω) (spectralZ E t) a b) := by
  refine ⟨?_, finDep_of_Hflow d n u (fun M => green M (spectralZ E t) a b),
    ⟨∅, 0, ((spectralZ E t).im)⁻¹, fun ω => ?_⟩⟩
  · exact Continuous.matrix_elem
      (continuous_green_comp (GreenDeriv_continuous_seqHflow d n u)
        (Sizes.seqHflow_isHermitian d n u) (zt_im_ne_zero_of_lt_one hE ht)) a b
  · simpa using norm_green_apply_le_etaT hE ht u a b ω

end Tame

/-! ### Step 2d: reading off one entry

Stein's identity is applied to scalar test functions, so the matrix-valued derivative of step 2a
has to be pushed through the evaluation map.  For the L2 operator norm that map is bounded with
constant one (`RBM.Ind.norm_apply_le_l2_opNorm`), hence a continuous linear map. -/

section Entry

/-- Reading off the `(a, b)` entry, as a bounded `ℝ`-linear map. -/
private noncomputable def entryCLM (n : Type*) [Fintype n] [DecidableEq n] (a b : n) :
    Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun M => M a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun M => by
      change ‖M a b‖ ≤ 1 * ‖M‖
      simpa using RBM.Ind.norm_apply_le_l2_opNorm M a b)

/-- **The coordinate derivative of a resolvent entry**.  This is the scalar statement Stein's
identity consumes. -/
theorem hasDerivAt_green_apply_update (d : Sizes) (n : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (ω : Sizes.SeqΩ d) {p : Coord (d.L n) (d.W n)} (hp : p ∈ usedCoords (d.L n) (d.W n))
    (a b : Idx (d.L n) (d.W n)) :
    HasDerivAt
      (fun t : ℝ => green (Sizes.seqHflow d n u (Function.update ω (crd d n p) t)) z a b)
      (-(Real.sqrt u) • (green (Sizes.seqHflow d n u ω) z
        * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2 * green (Sizes.seqHflow d n u ω) z) a b)
      (ω (crd d n p)) := by
  have h := hasDerivAt_green_Hflow_update d n u hz ω hp
  have h2 := (entryCLM (Idx (d.L n) (d.W n)) a b).hasFDerivAt.comp_hasDerivAt
    (ω (crd d n p)) h
  exact h2

end Entry

/-! ### Step 2e: the integration step

This is where the display stops being pathwise.  `RBM.Green.gaussIBP` replaces the Gaussian
coordinate `ω_c` by `gvar_c · ∂_c`, and `∂_c` of a resolvent entry is the sandwich of step 2a.
The only thing to check is that both sides are tame, and for the derivative that follows by
writing the sandwich as a double sum of entries. -/

section Integral

variable {d : Sizes} {n : ℕ} {E t : ℝ}

/-- A resolvent sandwich is tame: expand it as a double sum of products of entries. -/
theorem tame_green_mul_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (B : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (a b : Idx (d.L n) (d.W n)) :
    Tame d (fun ω : Sizes.SeqΩ d => (green (Sizes.seqHflow d n u ω) (spectralZ E t) * B
      * green (Sizes.seqHflow d n u ω) (spectralZ E t)) a b) := by
  have hfun : (fun ω : Sizes.SeqΩ d => (green (Sizes.seqHflow d n u ω) (spectralZ E t) * B
      * green (Sizes.seqHflow d n u ω) (spectralZ E t)) a b)
      = fun ω : Sizes.SeqΩ d => ∑ l : Idx (d.L n) (d.W n), ∑ k : Idx (d.L n) (d.W n),
        green (Sizes.seqHflow d n u ω) (spectralZ E t) a k * B k l
          * green (Sizes.seqHflow d n u ω) (spectralZ E t) l b := by
    funext ω
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
  rw [hfun]
  exact Tame.sum _ fun l _ => Tame.sum _ fun k _ =>
    ((tame_green_apply hE ht u a k).mul (Tame.const _)).mul (tame_green_apply hE ht u l b)

end Integral

/-! ### Step 2f: from one coordinate to a whole row

One matrix entry of `H` is carried by a *pair* of Gaussian coordinates (real and imaginary tag),
and the two tags have variance `S_ij/2` each.  Summing the one-coordinate identity of step 2e over
`usedCoords` therefore rebuilds `S_ij` exactly, while the two squared off-diagonal terms (the ones
carrying `c_b² = ±1`) cancel between the tags.  What survives is the paper's

  `E[(H_u G)_{aa}] = -u ∑_k S_{ak} E[G_{aa} G_{kk}]`,

here in the form `Σ_{p used} gvar_p (B_p (G B_p G))_{aa} = Σ_k svar(a,k) G_aa G_kk` for an
arbitrary complex matrix `G` (`sum_gvar_Bmat_sandwich_diag`).  The bookkeeping of the used
coordinates against the ordered pairs (`IBP_sum_used_eq_sum_pairs`) and the symmetries of `Bmat`
are private helpers here. -/

section Row

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
/-- The real direction is symmetric in the pair: `Bmat j i true = Bmat i j true`. -/
private theorem IBP_Bmat_swap_true (i j : Idx L W) :
    Bmat L W j i true = Bmat L W i j true := by
  ext k l
  rw [GreenDeriv_Bmat_apply, GreenDeriv_Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_left h1]
    · rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]

omit [NeZero L] [NeZero W] in
/-- The imaginary direction is antisymmetric in the pair (off the diagonal):
`Bmat j i false = -Bmat i j false`. -/
private theorem IBP_Bmat_swap_false {i j : Idx L W} (hij : i ≠ j) :
    Bmat L W j i false = -Bmat L W i j false := by
  ext k l
  change Bmat L W j i false k l = -(Bmat L W i j false k l)
  rw [GreenDeriv_Bmat_apply, GreenDeriv_Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · have h2 : ¬ (k = j ∧ l = i) := by
      rintro ⟨hkj, _⟩
      refine hij ?_
      rw [← h1.1]
      exact hkj
    rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1, neg_zero]

omit [NeZero L] [NeZero W] in
/-- The variance of a coordinate, read off from the index pair. -/
private theorem IBP_gvar_eq (p : Coord L W) :
    (gvar L W p : ℝ)
      = if p.1 = p.2.1 then svar L W p.1 p.2.1 else svar L W p.1 p.2.1 / 2 := by
  obtain ⟨i, j, b⟩ := p
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl]; exact gvar_diag L W i b
  · rw [ite_eq_right hij]; exact gvar_offDiag L W i j b hij

/-- Halving is injective on an `ℝ`-module: `X + X = Y + Y` forces `X = Y`. -/
private theorem IBP_eq_of_add_self_eq_add_self {V : Type*} [AddCommGroup V] [Module ℝ V]
    {X Y : V} (h : X + X = Y + Y) : X = Y := by
  have h2 : ((2 : ℝ)⁻¹ * 2) • X = ((2 : ℝ)⁻¹ * 2) • Y := by
    rw [mul_smul, mul_smul, two_smul, two_smul, h]
  have hc : ((2 : ℝ)⁻¹ * 2) = 1 := by norm_num
  rwa [hc, one_smul, one_smul] at h2

/-- The off-diagonal bookkeeping: a quarter of each of the two copies, twice over, is a half. -/
private theorem IBP_smul_quarter_pair {V : Type*} [AddCommGroup V] [Module ℝ V] (c : ℝ)
    (A B : V) :
    (c / 2) • A + (c / 2) • B =
      c • (1 / 4 : ℝ) • (A + B) + c • (1 / 4 : ℝ) • (A + B) := by
  rw [smul_smul, ← two_smul ℝ, smul_smul,
    show (2 * (c * (1 / 4)) : ℝ) = c / 2 by ring, smul_add]

/-- A double sum over a square index set is determined by the swap-symmetrization of its summand. -/
private theorem IBP_sum_sum_eq_of_swap_add_eq {ι : Type*} [Fintype ι] {V : Type*}
    [AddCommGroup V] [Module ℝ V] (g h : ι → ι → V)
    (key : ∀ i j, g i j + g j i = h i j + h j i) :
    (∑ i, ∑ j, g i j) = ∑ i, ∑ j, h i j := by
  have e1 : ∀ F : ι → ι → V,
      (∑ i, ∑ j, (F i j + F j i)) = (∑ i, ∑ j, F i j) + (∑ i, ∑ j, F j i) := by
    intro F
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  have hg : (∑ i, ∑ j, g i j) = ∑ i, ∑ j, g j i := Finset.sum_comm
  have hh : (∑ i, ∑ j, h i j) = ∑ i, ∑ j, h j i := Finset.sum_comm
  refine IBP_eq_of_add_self_eq_add_self ?_
  calc (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g i j)
      = (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g j i) := by rw [← hg]
    _ = ∑ i, ∑ j, (g i j + g j i) := (e1 g).symm
    _ = ∑ i, ∑ j, (h i j + h j i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h j i) := e1 h
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h i j) := by rw [← hh]

/-- **The bookkeeping lemma**.  Summing a
symmetric weight `S` against a symmetric family `f` over the "used" index set (one representative
per unordered pair, both tags, plus the diagonal with the real tag) equals the full double sum over
ordered pairs, with the diagonal treated separately and the off-diagonal terms weighted by `1/4`. -/
private theorem IBP_sum_used_eq_sum_pairs {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (κ : ι → ℕ) (hκ : Function.Injective κ)
    (S : ι → ι → ℝ) (hS : ∀ i j, S i j = S j i)
    (f : ι × ι × Bool → V)
    (htt : ∀ i j, f (i, j, true) = f (j, i, true))
    (hff : ∀ i j, f (i, j, false) = f (j, i, false)) :
    ∑ p ∈ Finset.univ.filter
        (fun p : ι × ι × Bool => κ p.1 < κ p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)),
      (if p.1 = p.2.1 then S p.1 p.2.1 else S p.1 p.2.1 / 2) • f p
      = ∑ i : ι, ∑ j : ι, S i j •
          (if i = j then f (i, i, true)
           else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine IBP_sum_sum_eq_of_swap_add_eq _ _ ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : ¬ (j = i) := fun hh => hij hh.symm
    rcases lt_trichotomy (κ i) (κ j) with hlt | heq | hgt
    · simp only [hij, hji, hlt, asymm hlt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero]
      exact IBP_smul_quarter_pair _ _ _
    · exact absurd (hκ heq) hij
    · simp only [hij, hji, hgt, asymm hgt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero, zero_add]
      exact IBP_smul_quarter_pair _ _ _

/-- `(B_p (G B_p G))_{aa}` is `(1 · B_p · (G B_p G))_{aa}`, the shape `mul_Bmat_mul_apply_of_ne`
consumes. -/
private theorem Bmat_mul_sandwich_diag_of_ne (G : Matrix (Idx L W) (Idx L W) ℂ) {x y : Idx L W}
    (hxy : x ≠ y) (b : Bool) (a : Idx L W) :
    (Bmat L W x y b * (G * Bmat L W x y b * G)) a a
      = (if b then (1 : ℂ) else Complex.I) * ((1 : Matrix (Idx L W) (Idx L W) ℂ) a x
          * (G * Bmat L W x y b * G) y a)
        + (if b then (1 : ℂ) else -Complex.I) * ((1 : Matrix (Idx L W) (Idx L W) ℂ) a y
          * (G * Bmat L W x y b * G) x a) := by
  have h := mul_Bmat_mul_apply_of_ne (M := (1 : Matrix (Idx L W) (Idx L W) ℂ))
    (M' := G * Bmat L W x y b * G) hxy b a a
  rw [Matrix.one_mul] at h
  exact h

/-- **The two tags of an off-diagonal coordinate**.  The squared off-diagonal terms carry opposite
signs and cancel; twice `G_{xx} G_{yy}`
survives. -/
private theorem Bmat_sandwich_diag_add_of_ne (G : Matrix (Idx L W) (Idx L W) ℂ) {x y : Idx L W}
    (hxy : x ≠ y) (a : Idx L W) :
    (Bmat L W x y true * (G * Bmat L W x y true * G)) a a
      + (Bmat L W x y false * (G * Bmat L W x y false * G)) a a
      = 2 * ((if a = x then G x x * G y y else 0) + (if a = y then G x x * G y y else 0)) := by
  have ht := Bmat_mul_sandwich_diag_of_ne G hxy true a
  have hf := Bmat_mul_sandwich_diag_of_ne G hxy false a
  have hKt := fun (p q : Idx L W) => mul_Bmat_mul_apply_of_ne (M := G) (M' := G) hxy true p q
  have hKf := fun (p q : Idx L W) => mul_Bmat_mul_apply_of_ne (M := G) (M' := G) hxy false p q
  rw [ht, hf, hKt, hKt, hKf, hKf]
  simp only [Bool.false_eq_true, reduceIte]
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := hxy
    rw [Matrix.one_apply_eq, Matrix.one_apply_ne hay, ite_eq_left rfl, ite_eq_right hay]
    ring_nf
    rw [Complex.I_sq]
    ring
  · by_cases hay : a = y
    · subst hay
      rw [Matrix.one_apply_eq, Matrix.one_apply_ne hax, ite_eq_left rfl, ite_eq_right hax]
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [Matrix.one_apply_ne hax, Matrix.one_apply_ne hay, ite_eq_right hax,
        ite_eq_right hay]
      ring

/-- **The diagonal coordinate**.
`B_{ii,true} = E_{ii}`, so the sandwich is a single square. -/
private theorem Bmat_sandwich_diag_diag (G : Matrix (Idx L W) (Idx L W) ℂ) (x a : Idx L W) :
    (Bmat L W x x true * (G * Bmat L W x x true * G)) a a
      = if a = x then G x x * G x x else 0 := by
  have h := mul_Bmat_mul_apply_diag (M := (1 : Matrix (Idx L W) (Idx L W) ℂ))
    (M' := G * Bmat L W x x true * G) x a a
  rw [Matrix.one_mul] at h
  rw [h, mul_Bmat_mul_apply_diag]
  by_cases hax : a = x
  · subst hax
    simp
  · simp [hax]

/-- The sandwich at a diagonal entry is symmetric under swapping the two indices of the
coordinate: it is quadratic in `B_p`, and the swap changes `B_p` by at most a sign. -/
private theorem Bmat_sandwich_diag_swap (G : Matrix (Idx L W) (Idx L W) ℂ) (x y : Idx L W)
    (b : Bool) (a : Idx L W) :
    (Bmat L W x y b * (G * Bmat L W x y b * G)) a a
      = (Bmat L W y x b * (G * Bmat L W y x b * G)) a a := by
  by_cases hxy : x = y
  · rw [hxy]
  · cases b with
    | true => rw [IBP_Bmat_swap_true x y]
    | false =>
      rw [IBP_Bmat_swap_false hxy]
      simp

/-- **The coordinate sum of the integration-by-parts display collapses to a row of `S`.**

`∑_{p ∈ usedCoords} gvar_p (B_p G B_p G)_{aa} = ∑_k svar_{ak} G_{aa} G_{kk}`: the two tags of an
off-diagonal coordinate each contribute `gvar = svar/2`, the squared off-diagonal terms cancel
between them, and the diagonal coordinate (real tag only, `gvar = svar`) supplies
`svar_{aa} G_{aa}²`.  `G` is an arbitrary complex matrix; only `svar_comm` is used. -/
private theorem IBP_sum_gvar_Bmat_sandwich_diag (G : Matrix (Idx L W) (Idx L W) ℂ)
    (a : Idx L W) :
    ∑ p ∈ usedCoords L W, (gvar L W p : ℝ) •
        (Bmat L W p.1 p.2.1 p.2.2 * (G * Bmat L W p.1 p.2.1 p.2.2 * G)) a a
      = ∑ k, (svar L W a k : ℂ) * (G a a * G k k) := by
  classical
  set f : Idx L W × Idx L W × Bool → ℂ :=
    fun p => (Bmat L W p.1 p.2.1 p.2.2 * (G * Bmat L W p.1 p.2.1 p.2.2 * G)) a a with hf
  have hgv : ∑ p ∈ usedCoords L W, (gvar L W p : ℝ) • f p
      = ∑ p ∈ usedCoords L W,
        (if p.1 = p.2.1 then svar L W p.1 p.2.1 else svar L W p.1 p.2.1 / 2) • f p :=
    Finset.sum_congr rfl fun p _ => by rw [IBP_gvar_eq]
  rw [hgv, show usedCoords L W = Finset.univ.filter
      (fun p : Idx L W × Idx L W × Bool =>
        idxKey L W p.1 < idxKey L W p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
    IBP_sum_used_eq_sum_pairs (idxKey L W) (idxKey_injective L W) (svar L W)
      (svar_comm L W) f
      (fun x y => Bmat_sandwich_diag_swap G x y true a)
      (fun x y => Bmat_sandwich_diag_swap G x y false a)]
  -- The term at `(x, y)` splits into the `x = a` half and the `y = a` half.
  have hterm : ∀ x y : Idx L W,
      (svar L W x y : ℝ) •
          (if x = y then f (x, x, true) else (1 / 4 : ℝ) • (f (x, y, true) + f (x, y, false)))
        = (if x = a then (2 : ℂ)⁻¹ * ((svar L W a y : ℂ) * (G a a * G y y)) else 0)
          + (if y = a then (2 : ℂ)⁻¹ * ((svar L W x a : ℂ) * (G x x * G a a))
              else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp only [hf, ite_true, Bmat_sandwich_diag_diag G x a, Complex.real_smul]
      by_cases hax : a = x
      · subst hax
        simp only [ite_true]
        ring
      · have hxa : ¬ (x = a) := fun h => hax h.symm
        simp only [ite_eq_right hax, ite_eq_right hxa]
        ring
    · simp only [hf, ite_eq_right hxy, Bmat_sandwich_diag_add_of_ne G hxy a, Complex.real_smul]
      by_cases hax : a = x
      · subst hax
        have hya : ¬ (y = a) := fun h => hxy h.symm
        simp only [ite_true, ite_eq_right hxy, ite_eq_right hya]
        push_cast
        ring
      · have hxa : ¬ (x = a) := fun h => hax h.symm
        by_cases hay : a = y
        · subst hay
          simp only [ite_true, ite_eq_right hax, ite_eq_right hxa]
          push_cast
          ring
        · have hya : ¬ (y = a) := fun h => hay h.symm
          simp only [ite_eq_right hax, ite_eq_right hay, ite_eq_right hxa, ite_eq_right hya]
          push_cast
          ring
  simp only [hterm, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y : Idx L W =>
      if x = a then (2 : ℂ)⁻¹ * ((svar L W a y : ℂ) * (G a a * G y y)) else 0)]
  simp only [Finset.sum_ite_eq' Finset.univ a, Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [svar_comm L W k a]
  ring

end Row

/-- **The coordinate sum of the integration-by-parts display collapses to a row of `S`.**  For an
arbitrary complex
matrix `G` (not assumed symmetric) and every `a`,
`∑_{p ∈ usedCoords} gvar_p (B_p (G B_p G))_{aa} = ∑_k svar(a,k) G_{aa} G_{kk}`. -/
theorem sum_gvar_Bmat_sandwich_diag (d : Sizes) (n : ℕ)
    (G : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (a : Idx (d.L n) (d.W n)) :
    ∑ p ∈ usedCoords (d.L n) (d.W n), (Sizes.seqGvar d (crd d n p) : ℝ) •
        (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
          * (G * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2 * G)) a a
      = ∑ k, (svar (d.L n) (d.W n) a k : ℂ) * (G a a * G k k) :=
  IBP_sum_gvar_Bmat_sandwich_diag G a

/-- The complex form of `sum_gvar_Bmat_sandwich_diag`. -/
theorem sum_gvar_Bmat_sandwich_diag_mul (d : Sizes) (n : ℕ)
    (G : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (a : Idx (d.L n) (d.W n)) :
    ∑ p ∈ usedCoords (d.L n) (d.W n), ((Sizes.seqGvar d (crd d n p) : ℝ) : ℂ) *
        (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
          * (G * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2 * G)) a a
      = ∑ k, (svar (d.L n) (d.W n) a k : ℂ) * (G a a * G k k) := by
  rw [← sum_gvar_Bmat_sandwich_diag d n G a]
  exact Finset.sum_congr rfl fun p _ => Complex.real_smul.symm

/-! ### Step 2f (continued): the whole row inside one integral

Multiplication by a constant matrix, and Stein's identity for `(B_p G)_{aa}`. -/

section IntegralRow

variable {d : Sizes} {n : ℕ} {E t : ℝ}

/-- `(B G)_{ac}` is tame for a constant `B`. -/
theorem tame_const_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (B : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (a c : Idx (d.L n) (d.W n)) :
    Tame d (fun ω : Sizes.SeqΩ d => (B * green (Sizes.seqHflow d n u ω) (spectralZ E t)) a c) := by
  have hfun : (fun ω : Sizes.SeqΩ d => (B * green (Sizes.seqHflow d n u ω) (spectralZ E t)) a c)
      = fun ω : Sizes.SeqΩ d =>
        ∑ l, B a l * green (Sizes.seqHflow d n u ω) (spectralZ E t) l c := by
    funext ω
    rw [Matrix.mul_apply]
  rw [hfun]
  exact Tame.sum _ fun l _ => (Tame.const _).mul (tame_green_apply hE ht u l c)

/-- `(B (G B G))_{ac}` is tame for a constant `B`. -/
theorem tame_const_mul_sandwich_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (B : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (a c : Idx (d.L n) (d.W n)) :
    Tame d (fun ω : Sizes.SeqΩ d => (B * (green (Sizes.seqHflow d n u ω) (spectralZ E t) * B
      * green (Sizes.seqHflow d n u ω) (spectralZ E t))) a c) := by
  have hfun : (fun ω : Sizes.SeqΩ d => (B * (green (Sizes.seqHflow d n u ω) (spectralZ E t) * B
      * green (Sizes.seqHflow d n u ω) (spectralZ E t))) a c)
      = fun ω : Sizes.SeqΩ d => ∑ l, B a l * (green (Sizes.seqHflow d n u ω) (spectralZ E t) * B
        * green (Sizes.seqHflow d n u ω) (spectralZ E t)) l c := by
    funext ω
    rw [Matrix.mul_apply]
  rw [hfun]
  exact Tame.sum _ fun l _ =>
    (Tame.const _).mul (tame_green_mul_mul_green_apply hE ht u B l c)

end IntegralRow

/-! ### Step 2g: the same, inside `E_i`

The display is a statement about `E_i`, not about `E`.  That costs nothing extra: `E_i` is
*itself* an integral against `Sizes.seqP d` of the integrand composed with `rowSplit`, and
`rowSplit` commutes with updating a row-`i` coordinate, so `gaussIBP` applies to it verbatim.
The only new input is that tameness survives freezing the coordinates off row `i`. -/

section CondIBP

variable {d : Sizes} {n : ℕ} {E t : ℝ}

/-- Updating a **row-`k`** coordinate commutes with the splitting: `rowSplit` reads that
coordinate from its second argument. -/
private theorem rowSplit_update (k : Idx (d.L n) (d.W n)) (ω ω' : Sizes.SeqΩ d)
    {c : Sizes.SeqCoord d} (hc : IsRowCoord d n k c) (s : ℝ) :
    rowSplit d n k ω (Function.update ω' c s) = Function.update (rowSplit d n k ω ω') c s := by
  funext e
  by_cases hec : e = c
  · subst hec
    rw [rowSplit_apply_of_isRowCoord k ω _ hc, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hec]
    unfold rowSplit
    split_ifs with h
    · rw [Function.update_of_ne hec]
    · rfl

/-- `ω' ↦ rowSplit k ω ω'` is continuous: every coordinate is either a projection or a
constant. -/
private theorem continuous_rowSplit_right (d : Sizes) (n : ℕ) (k : Idx (d.L n) (d.W n))
    (ω : Sizes.SeqΩ d) :
    Continuous fun ω' : Sizes.SeqΩ d => rowSplit d n k ω ω' := by
  refine continuous_pi fun c => ?_
  unfold rowSplit
  by_cases h : IsRowCoord d n k c
  · simpa [h] using continuous_apply c
  · simpa [h] using continuous_const (y := ω c)

/-- `polyW` of a split point is bounded by the product of the two `polyW`s. -/
private theorem polyW_rowSplit_le (k : Idx (d.L n) (d.W n)) (I : Finset (Sizes.SeqCoord d))
    (ω ω' : Sizes.SeqΩ d) :
    polyW I (rowSplit d n k ω ω') ≤ polyW I ω * polyW I ω' := by
  have hb : ∀ c ∈ I, |rowSplit d n k ω ω' c| ≤ |ω c| + |ω' c| := by
    intro c _
    unfold rowSplit
    split_ifs with h
    · have : (0 : ℝ) ≤ |ω c| := abs_nonneg _
      linarith
    · have : (0 : ℝ) ≤ |ω' c| := abs_nonneg _
      linarith
  have hsum : ∑ c ∈ I, |rowSplit d n k ω ω' c| ≤ (∑ c ∈ I, |ω c|) + ∑ c ∈ I, |ω' c| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hb
  have hA : (0 : ℝ) ≤ ∑ c ∈ I, |ω c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB : (0 : ℝ) ≤ ∑ c ∈ I, |ω' c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold polyW
  nlinarith

/-- **Tameness is preserved by freezing the coordinates off row `k`**. -/
private theorem Tame.comp_rowSplit {f : Sizes.SeqΩ d → ℂ} (hf : Tame d f)
    (k : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    Tame d (fun ω' : Sizes.SeqΩ d => f (rowSplit d n k ω ω')) := by
  obtain ⟨I, m, C, hb⟩ := hf.poly
  obtain ⟨J, hJ⟩ := hf.findep
  refine ⟨hf.cont.comp (continuous_rowSplit_right d n k ω), ⟨J, fun ω' ω'' h => ?_⟩,
    ⟨I, m, C * polyW I ω ^ m, fun ω' => ?_⟩⟩
  · refine hJ _ _ fun e he => ?_
    unfold rowSplit
    split_ifs with hrow
    · exact h e he
    · rfl
  · have hC : 0 ≤ C := by
      have hp : (0 : ℝ) < polyW I (fun _ => 0) ^ m := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (f fun _ => 0), hb fun _ => 0]
    have hle : polyW I (rowSplit d n k ω ω') ^ m ≤ polyW I ω ^ m * polyW I ω' ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (le_of_lt (polyW_pos _ _)) (polyW_rowSplit_le k I ω ω') m
    calc ‖f (rowSplit d n k ω ω')‖ ≤ C * polyW I (rowSplit d n k ω ω') ^ m :=
          hb (rowSplit d n k ω ω')
      _ ≤ C * (polyW I ω ^ m * polyW I ω' ^ m) := mul_le_mul_of_nonneg_left hle hC
      _ = C * polyW I ω ^ m * polyW I ω' ^ m := by ring

/-- **Gaussian integration by parts inside `E_k`**.  For a
coordinate of row `k`, `E_k` is an integral against the *same* product measure in the split
variable, so `gaussIBP` applies verbatim once the integrand is composed with `rowSplit`. -/
theorem condRow_coord_mul (hG : GaussIBP d) (k : Idx (d.L n) (d.W n))
    {c : Sizes.SeqCoord d} (hc : IsRowCoord d n k c) (g g' : Sizes.SeqΩ d → ℂ)
    (hg : Tame d g) (hg' : Tame d g')
    (hd : ∀ η : Sizes.SeqΩ d,
      HasDerivAt (fun s : ℝ => g (Function.update η c s)) (g' η) (η c))
    (ω : Sizes.SeqΩ d) :
    condRow d n k (fun η => (η c : ℂ) * g η) ω
      = (Sizes.seqGvar d c : ℝ) * condRow d n k g' ω := by
  rw [condRow_apply, condRow_apply]
  have hlhs : ∀ ω' : Sizes.SeqΩ d,
      ((rowSplit d n k ω ω' c : ℝ) : ℂ) * g (rowSplit d n k ω ω')
        = (ω' c : ℂ) * g (rowSplit d n k ω ω') := by
    intro ω'
    rw [rowSplit_apply_of_isRowCoord k ω ω' hc]
  simp only [hlhs]
  refine hG.stein c _ _ (hg.comp_rowSplit k ω) (hg'.comp_rowSplit k ω) fun ω' => ?_
  have hup : ∀ s : ℝ, g (rowSplit d n k ω (Function.update ω' c s))
      = g (Function.update (rowSplit d n k ω ω') c s) := by
    intro s
    rw [rowSplit_update k ω ω' hc s]
  have h := hd (rowSplit d n k ω ω')
  rw [rowSplit_apply_of_isRowCoord k ω ω' hc] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hup s)

/-! ### `E_k` is linear -/

/-- `E_k[c X] = c E_k[X]`. -/
theorem condRow_const_mul (k : Idx (d.L n) (d.W n)) (c : ℂ) (X : Sizes.SeqΩ d → ℂ)
    (ω : Sizes.SeqΩ d) :
    condRow d n k (fun η => c * X η) ω = c * condRow d n k X ω := by
  rw [condRow_apply, condRow_apply]
  exact integral_const_mul _ _

/-- `E_k[-(c X)] = -(c E_k[X])`. -/
theorem condRow_neg_const_mul (k : Idx (d.L n) (d.W n)) (c : ℂ) (X : Sizes.SeqΩ d → ℂ)
    (ω : Sizes.SeqΩ d) :
    condRow d n k (fun η => -(c * X η)) ω = -(c * condRow d n k X ω) := by
  rw [condRow_apply, condRow_apply, integral_neg, integral_const_mul]

/-- `E_k` commutes with finite sums of tame functions. -/
theorem condRow_finsetSum (hG : GaussIBP d) (k : Idx (d.L n) (d.W n)) {ι : Type*}
    (s : Finset ι) (F : ι → Sizes.SeqΩ d → ℂ) (hF : ∀ p ∈ s, Tame d (F p))
    (ω : Sizes.SeqΩ d) :
    condRow d n k (fun η => ∑ p ∈ s, F p η) ω = ∑ p ∈ s, condRow d n k (F p) ω := by
  simp only [condRow_apply]
  exact MeasureTheory.integral_finsetSum _
    fun p hp => ((hF p hp).comp_rowSplit k ω).integrable hG

/-- `E_k[0] = 0`. -/
theorem condRow_zero_apply (k : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    condRow d n k (fun _ => (0 : ℂ)) ω = 0 := by
  rw [condRow_apply, integral_zero]

/-! ### The coordinates that do not touch row `i` drop out -/

/-- `B_{xy,b}` has no entry in row `i` unless `i` is `x` or `y`. -/
theorem Bmat_mul_apply_diag_of_ne {L W : ℕ} [NeZero L] [NeZero W] {x y i : Idx L W}
    (hx : ¬ i = x) (hy : ¬ i = y) (b : Bool) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    (Bmat L W x y b * M) i i = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hx h.1), ite_eq_right (fun h => hy h.1),
    zero_mul]

/-! ### The conditional derivative of a row of the resolvent -/

/-- The coordinate derivative of `(B G)_{ac}` for a constant `B`. -/
theorem hasDerivAt_const_mul_green_apply_update (d : Sizes) (n : ℕ) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (η : Sizes.SeqΩ d) {p : Coord (d.L n) (d.W n)}
    (hp : p ∈ usedCoords (d.L n) (d.W n))
    (B : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (a c : Idx (d.L n) (d.W n)) :
    HasDerivAt
      (fun s : ℝ => (B * green (Sizes.seqHflow d n u (Function.update η (crd d n p) s)) z) a c)
      (-((Real.sqrt u : ℂ) * (B * (green (Sizes.seqHflow d n u η) z
        * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow d n u η) z)) a c)) (η (crd d n p)) := by
  have hterm : ∀ l : Idx (d.L n) (d.W n), HasDerivAt
      (fun s : ℝ => B a l
        * green (Sizes.seqHflow d n u (Function.update η (crd d n p) s)) z l c)
      (B a l * -((Real.sqrt u : ℂ) * (green (Sizes.seqHflow d n u η) z
        * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow d n u η) z) l c)) (η (crd d n p)) := by
    intro l
    have h := hasDerivAt_green_apply_update d n u hz η hp l c
    refine HasDerivAt.const_mul (B a l) ?_
    simpa [Complex.real_smul] using h
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Idx (d.L n) (d.W n))))
    (A := fun l (s : ℝ) => B a l
      * green (Sizes.seqHflow d n u (Function.update η (crd d n p) s)) z l c)
    (A' := fun l => B a l * -((Real.sqrt u : ℂ)
      * (green (Sizes.seqHflow d n u η) z * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow d n u η) z) l c))
    (fun l _ => hterm l)
  have hval : ∑ l : Idx (d.L n) (d.W n), B a l * -((Real.sqrt u : ℂ)
      * (green (Sizes.seqHflow d n u η) z * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow d n u η) z) l c)
      = -((Real.sqrt u : ℂ) * (B * (green (Sizes.seqHflow d n u η) z
        * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow d n u η) z)) a c) := by
    rw [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  exact (Matrix.mul_apply (M := B)
    (N := green (Sizes.seqHflow d n u (Function.update η (crd d n p) s)) z) (i := a) (k := c)).symm

/-! ### Step (b): the conditional integration by parts, one coordinate at a time -/

/-- **`E_i[ω_p (B_p G)_{ii}] = gvar_p E_i[-√u (B_p G B_p G)_{ii}]`**.  For a coordinate of row `i`
this is
`condRow_coord_mul`; for any other coordinate both sides vanish identically, because `B_p` has no
entry in row `i`. -/
theorem condRow_coord_mul_Bmat_mul_green_diag (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1)
    (u : ℝ) {p : Coord (d.L n) (d.W n)} (hp : p ∈ usedCoords (d.L n) (d.W n))
    (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    condRow d n i (fun η => (η (crd d n p) : ℂ)
        * (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
          * green (Sizes.seqHflow d n u η) (spectralZ E t)) i i) ω
      = (Sizes.seqGvar d (crd d n p) : ℝ) * condRow d n i (fun η => -((Real.sqrt u : ℂ)
          * (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
            * (green (Sizes.seqHflow d n u η) (spectralZ E t)
              * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
              * green (Sizes.seqHflow d n u η) (spectralZ E t))) i i)) ω := by
  obtain ⟨x, y, b⟩ := p
  by_cases hrow : IsRowCoord d n i (crd d n (x, y, b))
  · refine condRow_coord_mul hG i hrow _ _
      (tame_const_mul_green_apply hE ht u (Bmat (d.L n) (d.W n) x y b) i i)
      (((Tame.const (d := d) (Real.sqrt u : ℂ)).mul
        (tame_const_mul_sandwich_apply hE ht u (Bmat (d.L n) (d.W n) x y b) i i)).neg)
      (fun η => ?_) ω
    exact hasDerivAt_const_mul_green_apply_update d n u
      (zt_im_ne_zero_of_lt_one hE ht) η hp (Bmat (d.L n) (d.W n) x y b) i i
  · rw [crd, isRowCoord_mk] at hrow
    have hx : ¬ i = x := fun h => hrow (Or.inl h.symm)
    have hy : ¬ i = y := fun h => hrow (Or.inr h.symm)
    have hz1 : ∀ η : Sizes.SeqΩ d, (η (crd d n (x, y, b)) : ℂ)
        * (Bmat (d.L n) (d.W n) x y b
          * green (Sizes.seqHflow d n u η) (spectralZ E t)) i i = 0 := by
      intro η
      rw [Bmat_mul_apply_diag_of_ne hx hy b, mul_zero]
    have hz2 : ∀ η : Sizes.SeqΩ d, -((Real.sqrt u : ℂ)
        * (Bmat (d.L n) (d.W n) x y b * (green (Sizes.seqHflow d n u η) (spectralZ E t)
          * Bmat (d.L n) (d.W n) x y b
          * green (Sizes.seqHflow d n u η) (spectralZ E t))) i i) = 0 := by
      intro η
      rw [Bmat_mul_apply_diag_of_ne hx hy b, mul_zero, neg_zero]
    simp only [hz1, hz2, condRow_zero_apply, mul_zero]

/-- **Step (b): the conditional row identity**.

`E_i[(H_u G)_{ii}] = -u ∑_k S_{ik} E_i[G_{ii} G_{kk}]`: the whole-row Gaussian integration by
parts of the display, taken inside the conditional expectation `E_i`.  Only the coordinates of
row `i` occur (the others annihilate `B_p` in row `i`), and those are exactly the ones `E_i`
integrates out, so `condRow_coord_mul` applies to every surviving term. -/
theorem condRow_Hflow_mul_green_diag (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1)
    {u : ℝ} (hu : 0 ≤ u) (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    condRow d n i (fun η => (Sizes.seqHflow d n u η
        * green (Sizes.seqHflow d n u η) (spectralZ E t)) i i) ω
      = -((u : ℂ) * ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
          * condRow d n i (fun η => green (Sizes.seqHflow d n u η) (spectralZ E t) i i
              * green (Sizes.seqHflow d n u η) (spectralZ E t) k k) ω) := by
  classical
  have hsq : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
  have h1 : ∀ η : Sizes.SeqΩ d, (Sizes.seqHflow d n u η
      * green (Sizes.seqHflow d n u η) (spectralZ E t)) i i
      = ∑ p ∈ usedCoords (d.L n) (d.W n), (Real.sqrt u : ℂ) * ((η (crd d n p) : ℂ)
          * (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow d n u η) (spectralZ E t)) i i) := by
    intro η
    rw [GreenDeriv_seqHflow_eq_realSmul, GreenDeriv_seqXmat_eq_sum, Matrix.smul_mul,
      Finset.sum_mul]
    simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul,
      Finset.mul_sum]
  have htamep : ∀ p ∈ usedCoords (d.L n) (d.W n), Tame d
      (fun η : Sizes.SeqΩ d => (Real.sqrt u : ℂ) * ((η (crd d n p) : ℂ)
        * (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
          * green (Sizes.seqHflow d n u η) (spectralZ E t)) i i)) :=
    fun p _ => (Tame.const (d := d) (Real.sqrt u : ℂ)).mul
      ((Tame.coord (crd d n p)).mul
        (tame_const_mul_green_apply hE ht u (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2) i i))
  simp only [h1]
  rw [condRow_finsetSum hG i _ _ htamep]
  have hstep : ∀ p ∈ usedCoords (d.L n) (d.W n),
      condRow d n i (fun η => (Real.sqrt u : ℂ) * ((η (crd d n p) : ℂ)
          * (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow d n u η) (spectralZ E t)) i i)) ω
        = -((u : ℂ) * (((Sizes.seqGvar d (crd d n p) : ℝ) : ℂ)
            * condRow d n i (fun η => (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
              * (green (Sizes.seqHflow d n u η) (spectralZ E t)
                * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
                * green (Sizes.seqHflow d n u η) (spectralZ E t))) i i) ω)) := by
    intro p hp
    rw [condRow_const_mul, condRow_coord_mul_Bmat_mul_green_diag hG hE ht u hp i ω,
      condRow_neg_const_mul, ← hsq]
    ring
  rw [Finset.sum_congr rfl hstep]
  have htameq : ∀ p ∈ usedCoords (d.L n) (d.W n), Tame d
      (fun η : Sizes.SeqΩ d => ((Sizes.seqGvar d (crd d n p) : ℝ) : ℂ)
        * (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
          * (green (Sizes.seqHflow d n u η) (spectralZ E t)
            * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow d n u η) (spectralZ E t))) i i) :=
    fun p _ => (Tame.const (d := d) ((Sizes.seqGvar d (crd d n p) : ℝ) : ℂ)).mul
      (tame_const_mul_sandwich_apply hE ht u (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2) i i)
  have htamek : ∀ k ∈ (Finset.univ : Finset (Idx (d.L n) (d.W n))), Tame d
      (fun η : Sizes.SeqΩ d => (svar (d.L n) (d.W n) i k : ℂ)
        * (green (Sizes.seqHflow d n u η) (spectralZ E t) i i
          * green (Sizes.seqHflow d n u η) (spectralZ E t) k k)) :=
    fun k _ => (Tame.const (d := d) ((svar (d.L n) (d.W n) i k : ℝ) : ℂ)).mul
      ((tame_green_apply hE ht u i i).mul (tame_green_apply hE ht u k k))
  have hcollapse : ∑ p ∈ usedCoords (d.L n) (d.W n),
        ((Sizes.seqGvar d (crd d n p) : ℝ) : ℂ)
        * condRow d n i (fun η => (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
          * (green (Sizes.seqHflow d n u η) (spectralZ E t)
            * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow d n u η) (spectralZ E t))) i i) ω
      = ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
        * condRow d n i (fun η => green (Sizes.seqHflow d n u η) (spectralZ E t) i i
            * green (Sizes.seqHflow d n u η) (spectralZ E t) k k) ω := by
    have hL : ∑ p ∈ usedCoords (d.L n) (d.W n), ((Sizes.seqGvar d (crd d n p) : ℝ) : ℂ)
          * condRow d n i (fun η => (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
            * (green (Sizes.seqHflow d n u η) (spectralZ E t)
              * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
              * green (Sizes.seqHflow d n u η) (spectralZ E t))) i i) ω
        = condRow d n i (fun η => ∑ p ∈ usedCoords (d.L n) (d.W n),
            ((Sizes.seqGvar d (crd d n p) : ℝ) : ℂ)
            * (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
              * (green (Sizes.seqHflow d n u η) (spectralZ E t)
                * Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
                * green (Sizes.seqHflow d n u η) (spectralZ E t))) i i) ω := by
      rw [condRow_finsetSum hG i _ _ htameq]
      exact Finset.sum_congr rfl fun p _ => (condRow_const_mul _ _ _ _).symm
    have hR : ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
          * condRow d n i (fun η => green (Sizes.seqHflow d n u η) (spectralZ E t) i i
              * green (Sizes.seqHflow d n u η) (spectralZ E t) k k) ω
        = condRow d n i (fun η => ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
            * (green (Sizes.seqHflow d n u η) (spectralZ E t) i i
              * green (Sizes.seqHflow d n u η) (spectralZ E t) k k)) ω := by
      rw [condRow_finsetSum hG i _ _ htamek]
      exact Finset.sum_congr rfl fun k _ => (condRow_const_mul _ _ _ _).symm
    rw [hL, hR]
    simp only [sum_gvar_Bmat_sandwich_diag_mul d n _ i]
  rw [← hcollapse, Finset.sum_neg_distrib, ← Finset.mul_sum]

end CondIBP

/-! ### Step 3: the display, as an identity

Putting step 1 and step 2g together at the entry `(i,i)` gives the display with **no** error
term:

  `E_i(G_ii - m) = t m ∑_k S_ik E_i[G_ii (G_kk - m)]`.

Everything that is `O≺(Ψ²)` in the paper is the difference between this and the form the
fluctuation-averaging step asks for, namely `t m² ∑_k S_ik (G_kk - m)`; that difference is
isolated in the next section. -/

section CondDisplay

variable {d : Sizes} {n : ℕ} {E t : ℝ}

/-- The coordinate decomposition of `H_u M`, for an arbitrary right factor. -/
private theorem Hflow_mul_apply_eq_sum (d : Sizes) (n : ℕ) (u : ℝ) (η : Sizes.SeqΩ d)
    (M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ) (a c : Idx (d.L n) (d.W n)) :
    (Sizes.seqHflow d n u η * M) a c
      = ∑ p ∈ usedCoords (d.L n) (d.W n), (Real.sqrt u : ℂ)
          * ((η (crd d n p) : ℂ) * (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2 * M) a c) := by
  rw [GreenDeriv_seqHflow_eq_realSmul, GreenDeriv_seqXmat_eq_sum, Matrix.smul_mul,
    Finset.sum_mul]
  simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul,
    Finset.mul_sum]

/-- `(H_u G)_{ac}` is tame. -/
theorem tame_Hflow_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (a c : Idx (d.L n) (d.W n)) :
    Tame d (fun η : Sizes.SeqΩ d =>
      (Sizes.seqHflow d n u η * green (Sizes.seqHflow d n u η) (spectralZ E t)) a c) := by
  have hfun : (fun η : Sizes.SeqΩ d =>
      (Sizes.seqHflow d n u η * green (Sizes.seqHflow d n u η) (spectralZ E t)) a c)
      = fun η : Sizes.SeqΩ d => ∑ p ∈ usedCoords (d.L n) (d.W n), (Real.sqrt u : ℂ)
          * ((η (crd d n p) : ℂ) * (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow d n u η) (spectralZ E t)) a c) := by
    funext η
    exact Hflow_mul_apply_eq_sum d n u η _ a c
  rw [hfun]
  exact Tame.sum _ fun p _ => (Tame.const (d := d) (Real.sqrt u : ℂ)).mul
    ((Tame.coord (crd d n p)).mul
      (tame_const_mul_green_apply hE ht u (Bmat (d.L n) (d.W n) p.1 p.2.1 p.2.2) a c))

/-- `E_k` is additive on tame functions. -/
theorem condRow_tame_add (hG : GaussIBP d) (k : Idx (d.L n) (d.W n))
    {X Y : Sizes.SeqΩ d → ℂ} (hX : Tame d X) (hY : Tame d Y) (ω : Sizes.SeqΩ d) :
    condRow d n k (fun η => X η + Y η) ω = condRow d n k X ω + condRow d n k Y ω := by
  simp only [condRow_apply]
  exact integral_add ((hX.comp_rowSplit k ω).integrable hG)
    ((hY.comp_rowSplit k ω).integrable hG)

/-- `E_k` is subtractive on tame functions. -/
theorem condRow_tame_sub (hG : GaussIBP d) (k : Idx (d.L n) (d.W n))
    {X Y : Sizes.SeqΩ d → ℂ} (hX : Tame d X) (hY : Tame d Y) (ω : Sizes.SeqΩ d) :
    condRow d n k (fun η => X η - Y η) ω = condRow d n k X ω - condRow d n k Y ω := by
  simp only [condRow_apply]
  exact integral_sub ((hX.comp_rowSplit k ω).integrable hG)
    ((hY.comp_rowSplit k ω).integrable hG)

/-- **The row sums of the variance profile are `1`**, for `3 ≤ L`: `svar` is the real form of the
paper's covariance `Spaper` (`svar_cast_eq_Spaper`), whose rows sum to one (`RBM.sum_Spaper_row`;
five distinct residues of `sbSupport L`, which is why `3 ≤ L` is needed). -/
theorem IBP_sum_svar_row {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (i : Idx L W) :
    ∑ k : Idx L W, svar L W i k = 1 := by
  have h : ((∑ k : Idx L W, svar L W i k : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum]
    simp only [svar_cast_eq_Spaper]
    exact RBM.sum_Spaper_row L W hL i
  exact_mod_cast h

/-- **The display, exactly.**

`E_i(G_{ii} - m) = t m ∑_k S_{ik} E_i[G_{ii}(G_{kk} - m)]`.  This is an *identity*: no error
term, no stochastic domination.  It is `green_sub_smul_one_eq` at the entry `(i,i)`, the
conditional row integration by parts `condRow_Hflow_mul_green_diag`, and `∑_k S_{ik} = 1`
(`IBP_sum_svar_row`, which needs `3 ≤ L`, given by `d.three_le_L n`). -/
theorem condExpDiag_eq_sum_Sblk (hG : GaussIBP d) (hE : |E| < 2) (hE2 : |E| ≤ 2)
    (ht0 : 0 ≤ t) (ht : t < 1) (i : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    condExpDiag d n t (spectralZ E t) (spectralM E) i ω
      = (t : ℂ) * spectralM E * ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
          * condRow d n i (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
              * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E)) ω := by
  classical
  have hz := zt_im_ne_zero_of_lt_one (E := E) (t := t) hE ht
  -- the algebraic identity at the entry `(i, i)`
  have hpt : ∀ η : Sizes.SeqΩ d,
      greenDiagCentered d n t (spectralZ E t) (spectralM E) i η
      = (-(spectralM E)) * (Sizes.seqHflow d n t η
          * green (Sizes.seqHflow d n t η) (spectralZ E t)) i i
        + (-((t : ℂ) * spectralM E ^ 2)) * green (Sizes.seqHflow d n t η) (spectralZ E t) i i := by
    intro η
    have h := green_sub_smul_one_eq (Sizes.seqHflow_isHermitian d n t η) hE2 hz
    have hij := congrFun (congrFun h i) i
    rw [sub_smul_one_apply, ite_eq_left rfl] at hij
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul] at hij
    change green (Sizes.seqHflow d n t η) (spectralZ E t) i i - spectralM E = _
    rw [hij]
    ring
  -- `E_i` is linear
  have htame1 : Tame d
      (fun η : Sizes.SeqΩ d => (-(spectralM E)) * (Sizes.seqHflow d n t η
        * green (Sizes.seqHflow d n t η) (spectralZ E t)) i i) :=
    (Tame.const (d := d) (-(spectralM E))).mul (tame_Hflow_mul_green_apply hE ht t i i)
  have htame2 : Tame d
      (fun η : Sizes.SeqΩ d => (-((t : ℂ) * spectralM E ^ 2))
        * green (Sizes.seqHflow d n t η) (spectralZ E t) i i) :=
    (Tame.const (d := d) (-((t : ℂ) * spectralM E ^ 2))).mul (tame_green_apply hE ht t i i)
  have hlin : condExpDiag d n t (spectralZ E t) (spectralM E) i ω
      = (-(spectralM E)) * condRow d n i
          (fun η => (Sizes.seqHflow d n t η
            * green (Sizes.seqHflow d n t η) (spectralZ E t)) i i) ω
        + (-((t : ℂ) * spectralM E ^ 2)) * condRow d n i
          (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i) ω := by
    change condRow d n i (greenDiagCentered d n t (spectralZ E t) (spectralM E) i) ω = _
    have : (greenDiagCentered d n t (spectralZ E t) (spectralM E) i)
        = fun η => (-(spectralM E)) * (Sizes.seqHflow d n t η
            * green (Sizes.seqHflow d n t η) (spectralZ E t)) i i
          + (-((t : ℂ) * spectralM E ^ 2))
            * green (Sizes.seqHflow d n t η) (spectralZ E t) i i := funext hpt
    rw [this, condRow_tame_add hG i htame1 htame2, condRow_const_mul, condRow_const_mul]
  rw [hlin, condRow_Hflow_mul_green_diag hG hE ht ht0 i ω]
  -- `∑_k S_ik = 1` turns the lone `E_i[G_ii]` into a row sum
  have hrow : ∑ k, (svar (d.L n) (d.W n) i k : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, IBP_sum_svar_row (d.three_le_L n) i, Complex.ofReal_one]
  have hsplit : ∀ k : Idx (d.L n) (d.W n),
      condRow d n i (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
          * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E)) ω
        = condRow d n i (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
            * green (Sizes.seqHflow d n t η) (spectralZ E t) k k) ω
          - spectralM E * condRow d n i
            (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i) ω := by
    intro k
    have hA : Tame d (fun η : Sizes.SeqΩ d => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
        * green (Sizes.seqHflow d n t η) (spectralZ E t) k k) :=
      (tame_green_apply hE ht t i i).mul (tame_green_apply hE ht t k k)
    have hB : Tame d (fun η : Sizes.SeqΩ d =>
        spectralM E * green (Sizes.seqHflow d n t η) (spectralZ E t) i i) :=
      (Tame.const (d := d) (spectralM E)).mul (tame_green_apply hE ht t i i)
    have hfun : (fun η : Sizes.SeqΩ d => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
        * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E))
        = fun η : Sizes.SeqΩ d => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
            * green (Sizes.seqHflow d n t η) (spectralZ E t) k k
          - spectralM E * green (Sizes.seqHflow d n t η) (spectralZ E t) i i := by
      funext η; ring
    rw [hfun, condRow_tame_sub hG i hA hB, condRow_const_mul]
  have hsum : ∑ k, (svar (d.L n) (d.W n) i k : ℂ)
        * condRow d n i (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
            * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E)) ω
      = (∑ k, (svar (d.L n) (d.W n) i k : ℂ)
          * condRow d n i (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
              * green (Sizes.seqHflow d n t η) (spectralZ E t) k k) ω)
        - spectralM E * condRow d n i
          (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i) ω := by
    simp only [hsplit]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul]
  rw [hsum]
  ring

end CondDisplay

/-! ### Step 4: the remainder `ibpRem`

What is left is the difference between the identity of step 3 and the shape the
fluctuation-averaging step asks for.  It is isolated as `ibpRem`; the paper bounds it by `Ψ²`
in two pieces (`ibpRem_eq_add`).  The `≺` bookkeeping is not part of this file. -/

section Remainder

variable {d : Sizes} {n : ℕ} {E t : ℝ}

/-- **The remainder of the display** at the pair `(i, k)`:

  `E_i[G_{ii}(G_{kk} - m)] - m(G_{kk} - m)`.

This is the *only* thing between the identity `condExpDiag_eq_sum_Sblk` and the paper's
`t m² ∑_k S_ik (G_kk - m) + O≺(Ψ²)`.  The paper bounds it by `Ψ²` in two pieces
(`ibpRem_eq_add`): `E_i[(G_{ii}-m)(G_{kk}-m)]`, a product of two `Ψ`'s, and
`m(E_i(G_{kk}-m) - (G_{kk}-m))`, the minor-replacement error. -/
noncomputable def ibpRem (d : Sizes) (n : ℕ) (E t : ℝ)
    (q : Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) : ℂ :=
  condRow d n q.1 (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) q.1 q.1
      * (green (Sizes.seqHflow d n t η) (spectralZ E t) q.2 q.2 - spectralM E)) ω
    - spectralM E * (green (Sizes.seqHflow d n t ω) (spectralZ E t) q.2 q.2 - spectralM E)

/-- **The remainder splits into the paper's two `Ψ²` inputs**.

`E_i[G_{ii}(G_{kk}-m)] - m(G_{kk}-m) = E_i[(G_{ii}-m)(G_{kk}-m)] + m(E_i(G_{kk}-m) - (G_{kk}-m))`.

The first summand is a product of two entries of `G - m`; the second is the minor-replacement
error, since `G^{(i)}_{kk}` is `E_i`-invariant. -/
theorem ibpRem_eq_add (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1)
    (i k : Idx (d.L n) (d.W n)) (ω : Sizes.SeqΩ d) :
    ibpRem d n E t (i, k) ω
      = condRow d n i (fun η => (green (Sizes.seqHflow d n t η) (spectralZ E t) i i
            - spectralM E)
          * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E)) ω
        + spectralM E * (condRow d n i
            (greenDiagCentered d n t (spectralZ E t) (spectralM E) k) ω
          - (green (Sizes.seqHflow d n t ω) (spectralZ E t) k k - spectralM E)) := by
  have hA : Tame d (fun η : Sizes.SeqΩ d =>
      (green (Sizes.seqHflow d n t η) (spectralZ E t) i i - spectralM E)
      * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E)) :=
    ((tame_green_apply hE ht t i i).sub (Tame.const _)).mul
      ((tame_green_apply hE ht t k k).sub (Tame.const _))
  have hB : Tame d (fun η : Sizes.SeqΩ d => spectralM E
      * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E)) :=
    (Tame.const (d := d) (spectralM E)).mul ((tame_green_apply hE ht t k k).sub (Tame.const _))
  have hfun : (fun η : Sizes.SeqΩ d => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
      * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E))
      = fun η : Sizes.SeqΩ d => (green (Sizes.seqHflow d n t η) (spectralZ E t) i i
          - spectralM E)
          * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E)
        + spectralM E * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E) := by
    funext η
    ring
  have hgdc : (fun η : Sizes.SeqΩ d => spectralM E
      * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E))
      = fun η : Sizes.SeqΩ d => spectralM E
        * greenDiagCentered d n t (spectralZ E t) (spectralM E) k η := rfl
  change condRow d n i (fun η => green (Sizes.seqHflow d n t η) (spectralZ E t) i i
      * (green (Sizes.seqHflow d n t η) (spectralZ E t) k k - spectralM E)) ω
      - spectralM E * (green (Sizes.seqHflow d n t ω) (spectralZ E t) k k - spectralM E) = _
  rw [hfun, condRow_tame_add hG i hA hB, hgdc, condRow_const_mul]
  ring

end Remainder

end RBM.Green
