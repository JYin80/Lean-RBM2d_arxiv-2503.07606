/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.MLExpVocab

/-!
# Translation and negation invariance of the expected tensors (`ExpInvariant` of `ML:exp`)

Paper: Sections 5-6 (`eq:case4_B`, asserted there without proof) and Section 1 (`ML:exp`,
`eq:step6main`).

**Statement** (namespace `RBM.Evol`, `variable (d : Sizes)`): `expInvariant : ExpInvariant d`, the
statement of `Evolution/MLExpVocab.lean`: for every `n`, `|E| < 2`, `0 ≤ u < 1`,
`σ`, the expected tensors `f_{u,σ} = 𝔼(𝓛-𝒦)_{u,σ}` (`expErrT`) and
`D_{u,σ} = 𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)})_{u,σ}` (`expDriftT`) are invariant under every translation
`a ↦ a + v` and under the negation `a ↦ -a` of the labels (`TensorInvariant`).  Deterministic,
finite size; no hypothesis beyond the statement, no external input.

Argument (the helpers copy the proofs of the private lemmas named below).  Every
helper is `private`, prefixed `MLExpInv_`.
1. §1: an *automorphism* of `S^{(B)}` is a bijection `T` of `Z_L²` with
   `Ta - Tb ∈ sbSupport ↔ a - b ∈ sbSupport` (translations; the negation by `neg_mem_sbSupport`).
   Then `SB (Ta) (Tb) = SB a b`, `Θ_ξ (Ta) (Tb) = Θ_ξ a b` (the proof of `Theta_apply_add_right`,
   `Propagator/Basic.lean`, by uniqueness of the inverse) and, by `Kcal_two`,
   `𝒦_{u,(s₁,s₂),(Tx,Ty)} = 𝒦_{u,(s₁,s₂),(x,y)}` (`norm_xi`,
   `Loop/Kcal.lean`, gives `‖ξ‖ = u < 1`).  `𝒦` of length `3` is not needed: `egtN`
   contains `𝓛` and `avgErr` only.
2. §2: `T` acts on the fine lattice by `φ = split⁻¹ ∘ (T × id) ∘ split` (block label moved,
   offset kept; for the negation this is not the group negation of `Z_{WL}²`, which is not
   needed).  Then `S_{φi,φj} = S_{ij}`, `blockMat (M_{φ,φ}) = (blockMat M)_{ψ,ψ}`, and `Gsig`,
   `Eblk`, the trace, the matrix word of a loop, `𝓛`, `𝓛-𝒦` (length 2) and `⟨(G-m)E_x⟩` are
   equivariant: `𝓛_{σ,b}(M_{φ,φ}) = 𝓛_{σ,Tb}(M)`.
3. §3: `Xentry` is oriented by `idxKey`.  For any bijection `φ` of the fine lattice with
   `S_{φi,φj} = S_{ij}`, the coordinate map `(i,j,b) ↦ (φi,φj,b)` (orientation kept) or
   `(φj,φi,b)` (orientation reversed; the imaginary coordinate `b = false` changes sign) is a
   bijection `π` of `Coord L W` with `gvar ∘ π = gvar`, and `X(Φω) = X(ω)_{φ,φ}` for
   `Φω = (±ω ∘ π)`.
4. §4: for a family `φ m` over all sizes `m`, `Φ` is a measure-preserving measurable
   equivalence of the common sample space `SeqΩ d` (`infinitePi_map_piCongrLeft` for the
   reindexing of the coordinates, `infinitePi_map_pi` and `gaussianReal_map_neg` for the sign
   flips), so `𝔼F(H_u) = 𝔼F(H_u^{φ})` for *every* functional `F`
   (`MeasurePreserving.integral_comp'`: no measurability of `F` is needed).
5. §5: at `n = 2` the drift is an explicit window sum (`elklkN`: the single cut `(1,2)`;
   `egtN`: the cuts `k = 1,2`; the identities are copies of the private `MLExpDrift_elklkN_two`,
   `MLExpDrift_egtN_two`, `Evolution/MLExpDrift.lean`), and
   `Σ_{x,y} A_{Tx} S_{xy} B_{Ty} = Σ_{x,y} A_x S_{xy} B_y`.
6. §6: `expInvariant`; §8: public restatements of the automorphism machinery.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## 1. Automorphisms of `S^{(B)}` and the invariance of `Θ_ξ`, `𝒦` at length 2 -/

section Aut

variable {L : ℕ} [NeZero L]

/-- A bijection of `Z_L²` preserving the five-point relation `a - b ∈ sbSupport` (an automorphism
of `S^{(B)}`); translations and the negation are such. -/
private def MLExpInv_Aut (T : Z2 L ≃ Z2 L) : Prop :=
  ∀ a b : Z2 L, T a - T b ∈ sbSupport L ↔ a - b ∈ sbSupport L

private theorem MLExpInv_Aut_addRight (v : Z2 L) : MLExpInv_Aut (Equiv.addRight v) := by
  intro a b
  simp only [Equiv.coe_addRight, add_sub_add_right_eq_sub]

private theorem MLExpInv_Aut_neg : MLExpInv_Aut (Equiv.neg (Z2 L)) := by
  intro a b
  simp only [Equiv.neg_apply, neg_sub_neg]
  rw [← neg_sub, neg_mem_sbSupport]

private theorem MLExpInv_Aut_refl : MLExpInv_Aut (Equiv.refl (Z2 L)) := fun _ _ => Iff.rfl

private theorem MLExpInv_SB_apply {T : Z2 L ≃ Z2 L} (hT : MLExpInv_Aut T) (a b : Z2 L) :
    SB L (T a) (T b) = SB L a b := by
  simp only [SB_apply, sbKernel]
  exact if_congr (hT a b) rfl rfl

/-- `Θ_ξ` is invariant under every automorphism of `S^{(B)}` (properties 1-2 of `lem_propTH` for
the translations and the reflection; the proof of `Theta_apply_add_right`). -/
private theorem MLExpInv_Theta_apply (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_Aut T) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (a b : Z2 L) : Theta L ξ (T a) (T b) = Theta L ξ a b := by
  have hone : ((1 : Matrix (Z2 L) (Z2 L) ℂ)).submatrix T T = 1 := Matrix.submatrix_one_equiv T
  have hSB : (SB L).submatrix T T = SB L := by
    ext i j
    exact MLExpInv_SB_apply hT i j
  have hsub : (1 - ξ • SB L).submatrix T T = 1 - ξ • SB L := by
    simp [Matrix.submatrix_sub, Matrix.submatrix_smul, hSB, hone]
  have hkey : (Theta L ξ).submatrix T T = Theta L ξ := by
    refine eq_Theta_of_mul L hL hξ ?_
    calc (Theta L ξ).submatrix T T * (1 - ξ • SB L)
        = (Theta L ξ).submatrix T T * (1 - ξ • SB L).submatrix T T := by rw [hsub]
      _ = (Theta L ξ * (1 - ξ • SB L)).submatrix T T := Matrix.submatrix_mul_equiv _ _ _ _ _
      _ = 1 := by rw [Theta_mul L hL hξ, hone]
  exact congrFun (congrFun hkey a) b

private theorem MLExpInv_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖KLoop.mSig E s‖ = 1 := by
  cases s <;> simp [KLoop.mSig, Gauss.norm_spectralM hE]

private theorem MLExpInv_norm_xi {E t : ℝ} (hE : |E| ≤ 2) (ht : 0 ≤ t) (s s' : Bool) :
    ‖(t : ℂ) * (KLoop.mSig E s * KLoop.mSig E s')‖ = t := by
  rw [norm_mul, norm_mul, MLExpInv_norm_mSig hE, MLExpInv_norm_mSig hE, Complex.norm_real,
    Real.norm_of_nonneg ht, mul_one, mul_one]

/-- `𝒦` at length 2 is invariant under the relabelling of both labels (`(Kn2sol)`). -/
private theorem MLExpInv_Kcal_two (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_Aut T) (W : ℕ)
    {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) (s₁ s₂ : Bool) (x y : Z2 L) :
    KLoop.Kcal L W E t ⟨[s₁, s₂], [T x, T y]⟩ = KLoop.Kcal L W E t ⟨[s₁, s₂], [x, y]⟩ := by
  have hξ : ‖(t : ℂ) * (KLoop.mSig E s₁ * KLoop.mSig E s₂)‖ < 1 := by
    rw [MLExpInv_norm_xi hE.le ht0]; exact ht1
  rw [KLoop.Kcal_two, KLoop.Kcal_two, MLExpInv_Theta_apply hL hT hξ]

end Aut

/-! ## 2. The relabelling of the fine lattice and the equivariance of the matrix-level functionals -/

section Mat

variable {L : ℕ} [NeZero L] (W : ℕ) [NeZero W]

/-- `(a, o) ↦ (T a, o)` on block labels and offsets. -/
private def MLExpInv_psi (T : Z2 L ≃ Z2 L) : BlockIndex L W ≃ BlockIndex L W :=
  Equiv.prodCongr T (Equiv.refl _)

/-- The relabelling of the fine lattice `Z_{WL}²` that moves the block label by `T` and keeps the
offset. -/
private def MLExpInv_phi (T : Z2 L ≃ Z2 L) : Idx L W ≃ Idx L W :=
  ((splitEquiv L W).trans (MLExpInv_psi W T)).trans (splitEquiv L W).symm

private theorem MLExpInv_split_phi (T : Z2 L ≃ Z2 L) (i : Idx L W) :
    split L W (MLExpInv_phi W T i) = MLExpInv_psi W T (split L W i) := by
  have h : splitEquiv L W (MLExpInv_phi W T i) = MLExpInv_psi W T (splitEquiv L W i) := by
    simp [MLExpInv_phi]
  exact h

/-- The variance profile `S_ij` is invariant under the relabelling. -/
private theorem MLExpInv_svar_phi {T : Z2 L ≃ Z2 L} (hT : MLExpInv_Aut T) (i j : Idx L W) :
    svar L W (MLExpInv_phi W T i) (MLExpInv_phi W T j) = svar L W i j := by
  have hi : (blk L W (MLExpInv_phi W T i).1, blk L W (MLExpInv_phi W T i).2) =
      T (blk L W i.1, blk L W i.2) := congrArg Prod.fst (MLExpInv_split_phi W T i)
  have hj : (blk L W (MLExpInv_phi W T j).1, blk L W (MLExpInv_phi W T j).2) =
      T (blk L W j.1, blk L W j.2) := congrArg Prod.fst (MLExpInv_split_phi W T j)
  unfold svar
  rw [hi, hj]
  exact if_congr (hT _ _) rfl rfl

private theorem MLExpInv_blockMat_submatrix (T : Z2 L ≃ Z2 L) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    blockMat (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T)) =
      (blockMat M).submatrix (MLExpInv_psi W T) (MLExpInv_psi W T) := by
  unfold blockMat
  rw [Matrix.submatrix_submatrix, Matrix.submatrix_submatrix]
  have h : ⇑(MLExpInv_phi W T) ∘ ⇑(splitEquiv L W).symm = ⇑(splitEquiv L W).symm ∘ ⇑(MLExpInv_psi W T) := by
    funext b
    simp [MLExpInv_phi]
  rw [h]

private theorem MLExpInv_green_submatrix (T : Z2 L ≃ Z2 L)
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (w : ℂ) :
    green (H.submatrix (MLExpInv_psi W T) (MLExpInv_psi W T)) w =
      (green H w).submatrix (MLExpInv_psi W T) (MLExpInv_psi W T) := by
  unfold green
  have h : H.submatrix (MLExpInv_psi W T) (MLExpInv_psi W T) - w • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =
      (H - w • 1).submatrix (MLExpInv_psi W T) (MLExpInv_psi W T) := by
    simp [Matrix.submatrix_sub, Matrix.submatrix_smul]
  rw [h, Matrix.inv_submatrix_equiv]

private theorem MLExpInv_Gsig_submatrix (T : Z2 L ≃ Z2 L)
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (s : Bool) :
    Gsig (H.submatrix (MLExpInv_psi W T) (MLExpInv_psi W T)) z s =
      (Gsig H z s).submatrix (MLExpInv_psi W T) (MLExpInv_psi W T) := by
  unfold Gsig
  exact MLExpInv_green_submatrix W T H _

private theorem MLExpInv_Eblk_submatrix (T : Z2 L ≃ Z2 L) (a : Z2 L) :
    (Eblk L W (T a)).submatrix (MLExpInv_psi W T) (MLExpInv_psi W T) = Eblk L W a := by
  unfold Eblk
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext p
  simp [MLExpInv_psi]

private theorem MLExpInv_trace_submatrix {m : Type*} [Fintype m] (e : m ≃ m) (A : Matrix m m ℂ) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => A i i)

/-- The matrix word of a loop, under the relabelling of the block indices. -/
private theorem MLExpInv_foldr (T : Z2 L ≃ Z2 L) (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ)
    (z : ℂ) (l : List (Bool × Z2 L)) :
    l.foldr (fun (p : Bool × Z2 L) (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =>
        Gsig (H.submatrix (MLExpInv_psi W T) (MLExpInv_psi W T)) z p.1 * Eblk L W p.2 * M) 1 =
      ((l.map (fun p : Bool × Z2 L => (p.1, T p.2))).foldr
        (fun (p : Bool × Z2 L) (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =>
          Gsig H z p.1 * Eblk L W p.2 * M) 1).submatrix (MLExpInv_psi W T) (MLExpInv_psi W T) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldr_cons, List.map_cons, ih]
    rw [← MLExpInv_Eblk_submatrix W T p.2, MLExpInv_Gsig_submatrix]
    simp only [Matrix.submatrix_mul_equiv]

private theorem MLExpInv_gloop_submatrix (T : Z2 L ≃ Z2 L)
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (I : LoopIdx (Z2 L)) :
    gloop L W (H.submatrix (MLExpInv_psi W T) (MLExpInv_psi W T)) z I =
      gloop L W H z ⟨I.σ, I.a.map T⟩ := by
  unfold gloop gloopProd
  rw [MLExpInv_foldr, MLExpInv_trace_submatrix, List.zip_map_right]
  rfl

private theorem MLExpInv_gloop_loopOf {k : ℕ} (T : Z2 L ≃ Z2 L)
    (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (σ : Fin k → Bool) (b : Fin k → Z2 L) :
    gloop L W (H.submatrix (MLExpInv_psi W T) (MLExpInv_psi W T)) z (loopOf σ b) =
      gloop L W H z (loopOf σ (fun i => T (b i))) := by
  rw [MLExpInv_gloop_submatrix]
  simp only [loopOf, List.map_ofFn]
  rfl

/-- `𝓛` at the relabelled matrix: `𝓛_{u,σ,b}(M^φ) = 𝓛_{u,σ,T b}(M)`. -/
private theorem MLExpInv_LLf {k : ℕ} (T : Z2 L ≃ Z2 L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin k → Bool) (b : Fin k → Z2 L) :
    LLf L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T)) (loopOf σ b) =
      LLf L W E u M (loopOf σ (fun i => T (b i))) := by
  unfold LLf
  rw [MLExpInv_blockMat_submatrix, MLExpInv_gloop_loopOf]

/-- `(𝓛 - 𝒦)` at length 2. -/
private theorem MLExpInv_LKf (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_Aut T) {E u : ℝ}
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (b : Fin 2 → Z2 L) :
    LKf L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T)) (loopOf σ b) =
      LKf L W E u M (loopOf σ (fun i => T (b i))) := by
  unfold LKf
  rw [MLExpInv_LLf]
  congr 1
  exact (MLExpInv_Kcal_two hL hT W hE hu0 hu1 (σ 0) (σ 1) (b 0) (b 1)).symm

/-- `⟨(G - m) E_x⟩` at the relabelled matrix. -/
private theorem MLExpInv_avgErr (T : Z2 L ≃ Z2 L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (s : Bool) (x : Z2 L) :
    avgErr L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T)) s x =
      avgErr L W E u M s (T x) := by
  unfold avgErr greenBlk
  rw [MLExpInv_blockMat_submatrix, MLExpInv_Gsig_submatrix, ← MLExpInv_Eblk_submatrix W T x]
  have h : (Gsig (blockMat M) (spectralZ E u) s).submatrix (MLExpInv_psi W T) (MLExpInv_psi W T) -
      KLoop.mSig E s • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =
      (Gsig (blockMat M) (spectralZ E u) s - KLoop.mSig E s • 1).submatrix (MLExpInv_psi W T)
        (MLExpInv_psi W T) := by
    simp [Matrix.submatrix_sub, Matrix.submatrix_smul]
  rw [h, Matrix.submatrix_mul_equiv, MLExpInv_trace_submatrix]

end Mat

/-! ## 3. The coordinate map of the Gaussian sample space

For a bijection `φ` of the fine lattice with `S_{φi,φj} = S_{ij}`, the coordinates
`(i,j,b) ↦ s(i,j,b) ω(π(i,j,b))` (a coordinate bijection `π` and sign flips `s`) give a
sample `Φω` with `X(Φω) = X(ω)_{φ,φ}` (the orientation of `Xentry` by `idxKey` is the only
obstruction; `π` swaps the pair where `φ` reverses the orientation, and the imaginary coordinate
changes sign there). -/

section Coord

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `φ` keeps the `idxKey`-orientation of the pair `(i,j)`. -/
private def MLExpInv_pres (φ : Idx L W ≃ Idx L W) (i j : Idx L W) : Prop :=
  idxKey L W i < idxKey L W j ↔ idxKey L W (φ i) < idxKey L W (φ j)

private instance MLExpInv_pres_dec (φ : Idx L W ≃ Idx L W) (i j : Idx L W) :
    Decidable (MLExpInv_pres φ i j) := by
  unfold MLExpInv_pres; infer_instance

private theorem MLExpInv_pres_self (φ : Idx L W ≃ Idx L W) (i : Idx L W) : MLExpInv_pres φ i i := by
  unfold MLExpInv_pres; simp

private theorem MLExpInv_pres_comm (φ : Idx L W ≃ Idx L W) {i j : Idx L W}
    (h : MLExpInv_pres φ i j) : MLExpInv_pres φ j i := by
  by_cases hij : i = j
  · subst hij; exact h
  · have hk : idxKey L W i ≠ idxKey L W j := fun e => hij (idxKey_injective L W e)
    have hk' : idxKey L W (φ i) ≠ idxKey L W (φ j) := fun e =>
      hij (φ.injective (idxKey_injective L W e))
    unfold MLExpInv_pres at h ⊢
    omega

/-- The coordinate map: `(i,j,b) ↦ (φi, φj, b)` if `φ` keeps the orientation of `(i,j)`, else
`(φj, φi, b)`. -/
private def MLExpInv_piFun (φ : Idx L W ≃ Idx L W) (c : Coord L W) : Coord L W :=
  if MLExpInv_pres φ c.1 c.2.1 then (φ c.1, φ c.2.1, c.2.2) else (φ c.2.1, φ c.1, c.2.2)

private theorem MLExpInv_piFun_pos (φ : Idx L W ≃ Idx L W) {i j : Idx L W}
    (h : MLExpInv_pres φ i j) (b : Bool) : MLExpInv_piFun φ (i, j, b) = (φ i, φ j, b) := by
  simp [MLExpInv_piFun, h]

private theorem MLExpInv_piFun_neg (φ : Idx L W ≃ Idx L W) {i j : Idx L W}
    (h : ¬ MLExpInv_pres φ i j) (b : Bool) : MLExpInv_piFun φ (i, j, b) = (φ j, φ i, b) := by
  simp [MLExpInv_piFun, h]

private theorem MLExpInv_piFun_injective (φ : Idx L W ≃ Idx L W) :
    Function.Injective (MLExpInv_piFun φ) := by
  rintro ⟨i, j, b⟩ ⟨i', j', b'⟩ h
  by_cases h1 : MLExpInv_pres φ i j <;> by_cases h2 : MLExpInv_pres φ i' j'
  · rw [MLExpInv_piFun_pos φ h1, MLExpInv_piFun_pos φ h2] at h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  · rw [MLExpInv_piFun_pos φ h1, MLExpInv_piFun_neg φ h2] at h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨e1, e2, e3⟩ := h
    subst e1 e2
    exact absurd (MLExpInv_pres_comm φ h1) h2
  · rw [MLExpInv_piFun_neg φ h1, MLExpInv_piFun_pos φ h2] at h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨e1, e2, e3⟩ := h
    subst e1 e2
    exact absurd (MLExpInv_pres_comm φ h2) h1
  · rw [MLExpInv_piFun_neg φ h1, MLExpInv_piFun_neg φ h2] at h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; rfl

/-- The coordinate bijection. -/
private def MLExpInv_pi (φ : Idx L W ≃ Idx L W) : Coord L W ≃ Coord L W :=
  Equiv.ofBijective (MLExpInv_piFun φ)
    (Finite.injective_iff_bijective.mp (MLExpInv_piFun_injective φ))

private theorem MLExpInv_pi_apply (φ : Idx L W ≃ Idx L W) (c : Coord L W) :
    MLExpInv_pi φ c = MLExpInv_piFun φ c := rfl

/-- The coordinate variance is invariant under the coordinate bijection. -/
private theorem MLExpInv_gvar_pi (φ : Idx L W ≃ Idx L W)
    (hφ : ∀ i j, svar L W (φ i) (φ j) = svar L W i j) (c : Coord L W) :
    gvar L W (MLExpInv_pi φ c) = gvar L W c := by
  apply NNReal.eq
  obtain ⟨i, j, b⟩ := c
  rw [MLExpInv_pi_apply]
  by_cases hij : i = j
  · subst hij
    rw [MLExpInv_piFun_pos φ (MLExpInv_pres_self φ i), gvar_diag, gvar_diag, hφ]
  · have hne : φ i ≠ φ j := fun h => hij (φ.injective h)
    by_cases h : MLExpInv_pres φ i j
    · rw [MLExpInv_piFun_pos φ h, gvar_offDiag L W _ _ _ hne, gvar_offDiag L W _ _ _ hij, hφ]
    · rw [MLExpInv_piFun_neg φ h, gvar_offDiag L W _ _ _ hne.symm, gvar_offDiag L W _ _ _ hij,
        hφ, svar_comm L W j i]

/-- The coordinates whose sign is reversed: `(i,j,false)` with reversed orientation. -/
private def MLExpInv_flip (φ : Idx L W ≃ Idx L W) (c : Coord L W) : Prop :=
  ¬ MLExpInv_pres φ c.1 c.2.1 ∧ c.2.2 = false

private instance MLExpInv_flip_dec (φ : Idx L W ≃ Idx L W) (c : Coord L W) :
    Decidable (MLExpInv_flip φ c) := by
  unfold MLExpInv_flip; infer_instance

/-- The transformed sample `Φω`. -/
private def MLExpInv_Phi (φ : Idx L W ≃ Idx L W) (ω : Ω L W) : Ω L W := fun c =>
  if MLExpInv_flip φ c then -ω (MLExpInv_pi φ c) else ω (MLExpInv_pi φ c)

private theorem MLExpInv_Phi_true (φ : Idx L W ≃ Idx L W) (ω : Ω L W) (i j : Idx L W) :
    MLExpInv_Phi φ ω (i, j, true) =
      if MLExpInv_pres φ i j then ω (φ i, φ j, true) else ω (φ j, φ i, true) := by
  have hf : ¬ MLExpInv_flip φ (i, j, true) := fun h => by
    have := h.2; simp at this
  unfold MLExpInv_Phi
  rw [ite_eq_right hf, MLExpInv_pi_apply]
  by_cases h : MLExpInv_pres φ i j
  · rw [MLExpInv_piFun_pos φ h, ite_eq_left h]
  · rw [MLExpInv_piFun_neg φ h, ite_eq_right h]

private theorem MLExpInv_Phi_false (φ : Idx L W ≃ Idx L W) (ω : Ω L W) (i j : Idx L W) :
    MLExpInv_Phi φ ω (i, j, false) =
      if MLExpInv_pres φ i j then ω (φ i, φ j, false) else -ω (φ j, φ i, false) := by
  unfold MLExpInv_Phi
  rw [MLExpInv_pi_apply]
  by_cases h : MLExpInv_pres φ i j
  · have hf : ¬ MLExpInv_flip φ (i, j, false) := fun hh => hh.1 h
    rw [ite_eq_right hf, MLExpInv_piFun_pos φ h, ite_eq_left h]
  · have hf : MLExpInv_flip φ (i, j, false) := ⟨h, rfl⟩
    rw [ite_eq_left hf, MLExpInv_piFun_neg φ h, ite_eq_right h]

/-- The oriented matrix entries of `Φω` are the entries of `ω` at the relabelled indices. -/
private theorem MLExpInv_Xentry (φ : Idx L W ≃ Idx L W) (ω : Ω L W) (i j : Idx L W) :
    Xentry L W (MLExpInv_Phi φ ω) i j = Xentry L W ω (φ i) (φ j) := by
  have hinj : ∀ x y : Idx L W, idxKey L W x = idxKey L W y → x = y :=
    fun x y h => idxKey_injective L W h
  unfold Xentry
  rcases lt_trichotomy (idxKey L W i) (idxKey L W j) with hij | hij | hij
  · rcases lt_trichotomy (idxKey L W (φ i)) (idxKey L W (φ j)) with h' | h' | h'
    · have hp : MLExpInv_pres φ i j := by unfold MLExpInv_pres; omega
      rw [ite_eq_left hij, ite_eq_left h', MLExpInv_Phi_true, MLExpInv_Phi_false,
        ite_eq_left hp, ite_eq_left hp]
    · exfalso
      have h1 : φ i = φ j := hinj _ _ h'
      have h2 := φ.injective h1
      subst h2
      exact lt_irrefl _ hij
    · have hp : ¬ MLExpInv_pres φ i j := by unfold MLExpInv_pres; omega
      rw [ite_eq_left hij, ite_eq_right (not_lt.2 h'.le), ite_eq_left h', MLExpInv_Phi_true,
        MLExpInv_Phi_false, ite_eq_right hp, ite_eq_right hp]
      push_cast; ring
  · have hi : i = j := hinj _ _ hij
    subst hi
    have hp := MLExpInv_pres_self φ i
    rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _),
      ite_eq_right (lt_irrefl _), MLExpInv_Phi_true, ite_eq_left hp]
  · rcases lt_trichotomy (idxKey L W (φ i)) (idxKey L W (φ j)) with h' | h' | h'
    · have hp : ¬ MLExpInv_pres φ j i := by unfold MLExpInv_pres; omega
      rw [ite_eq_right (not_lt.2 hij.le), ite_eq_left hij, ite_eq_left h', MLExpInv_Phi_true,
        MLExpInv_Phi_false, ite_eq_right hp, ite_eq_right hp]
      push_cast; ring
    · exfalso
      have h1 : φ i = φ j := hinj _ _ h'
      have h2 := φ.injective h1
      subst h2
      exact lt_irrefl _ hij
    · have hp : MLExpInv_pres φ j i := by unfold MLExpInv_pres; omega
      rw [ite_eq_right (not_lt.2 hij.le), ite_eq_left hij, ite_eq_right (not_lt.2 h'.le),
        ite_eq_left h', MLExpInv_Phi_true, MLExpInv_Phi_false, ite_eq_left hp, ite_eq_left hp]

/-- `X(Φω) = X(ω)_{φ,φ}` as matrices. -/
private theorem MLExpInv_Xmat (φ : Idx L W ≃ Idx L W) (ω : Ω L W) :
    Xmat L W (MLExpInv_Phi φ ω) = (Xmat L W ω).submatrix φ φ := by
  ext i j
  exact MLExpInv_Xentry φ ω i j

end Coord

/-! ## 4. The measure-preserving relabelling of the common sample space -/

section Seq

variable (d : Sizes)

/-- **The change of variables**: for a family of bijections `φ m` of the fine lattices with
`S_{φi,φj} = S_{ij}`, there is a measure-preserving measurable equivalence `Φ` of the common sample
space `SeqΩ d` (`seqP d`, the product of independent centred Gaussians) whose size-`m` slice is
`MLExpInv_Phi (φ m)`.  It is the composition of the reindexing of the coordinates by the
bijection `Ψ` (`π m` on the `m`-th block of coordinates) and of the sign flips
(`gaussianReal 0 v` is symmetric). -/
private theorem MLExpInv_seq (φ : ∀ m, Idx (d.L m) (d.W m) ≃ Idx (d.L m) (d.W m))
    (hφ : ∀ m i j, svar (d.L m) (d.W m) (φ m i) (φ m j) = svar (d.L m) (d.W m) i j) :
    ∃ Φ : Sizes.SeqΩ d ≃ᵐ Sizes.SeqΩ d, MeasurePreserving Φ (Sizes.seqP d) (Sizes.seqP d) ∧
      ∀ (m : ℕ) (ω : Sizes.SeqΩ d),
        Sizes.slice d m (Φ ω) = MLExpInv_Phi (φ m) (Sizes.slice d m ω) := by
  classical
  let Ψ : Sizes.SeqCoord d ≃ Sizes.SeqCoord d :=
    Equiv.sigmaCongrRight (fun m => MLExpInv_pi (φ m))
  let fl : Sizes.SeqCoord d → Prop := fun c => MLExpInv_flip (φ c.1) c.2
  let μ : Sizes.SeqCoord d → Measure ℝ := fun c => gaussianReal 0 (Sizes.seqGvar d c)
  let e1 : Sizes.SeqΩ d ≃ᵐ Sizes.SeqΩ d :=
    MeasurableEquiv.piCongrLeft (fun _ : Sizes.SeqCoord d => ℝ) Ψ.symm
  let e2 : Sizes.SeqΩ d ≃ᵐ Sizes.SeqΩ d :=
    MeasurableEquiv.piCongrRight
      (fun c => if fl c then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ)
  have hg : ∀ c, Sizes.seqGvar d (Ψ c) = Sizes.seqGvar d c := by
    rintro ⟨m, c⟩
    exact MLExpInv_gvar_pi (φ m) (hφ m) c
  have hP : Sizes.seqP d = Measure.infinitePi μ := rfl
  have he1 : ∀ (ω : Sizes.SeqΩ d) (c : Sizes.SeqCoord d), e1 ω c = ω (Ψ c) := by
    intro ω c
    obtain ⟨a, rfl⟩ := Ψ.symm.surjective c
    rw [Equiv.apply_symm_apply]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Sizes.SeqCoord d => ℝ) Ψ.symm ω a
  have he2 : ∀ (x : Sizes.SeqΩ d) (c : Sizes.SeqCoord d),
      e2 x c = (if fl c then (fun y : ℝ => -y) else (fun y : ℝ => y)) (x c) := by
    intro x c
    change (if fl c then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ) (x c) = _
    by_cases hc : fl c <;> simp [hc]
  have h1 : Measure.map e1 (Sizes.seqP d) = Sizes.seqP d := by
    have h := Measure.infinitePi_map_piCongrLeft (X := fun _ : Sizes.SeqCoord d => ℝ) μ Ψ.symm
    have hμ : (fun i => μ (Ψ.symm i)) = μ := by
      funext i
      have h' := hg (Ψ.symm i)
      rw [Equiv.apply_symm_apply] at h'
      simp only [μ, h']
    rw [hμ] at h
    rw [hP]
    exact h
  have h2 : Measure.map e2 (Sizes.seqP d) = Sizes.seqP d := by
    have h := Measure.infinitePi_map_pi (X := fun _ : Sizes.SeqCoord d => ℝ) μ
      (f := fun c => if fl c then (fun x : ℝ => -x) else (fun x : ℝ => x))
      (fun c => by
        by_cases hc : fl c
        · simp only [hc, ite_true]; fun_prop
        · simp only [hc, ite_false]; fun_prop)
    have hμ : (fun c => (μ c).map (if fl c then (fun x : ℝ => -x) else (fun x : ℝ => x))) = μ := by
      funext c
      by_cases hc : fl c
      · simp only [hc, ite_true, μ, gaussianReal_map_neg, neg_zero]
      · simp only [hc, ite_false, Measure.map_id']
    rw [hμ] at h
    have hfun : (⇑e2 : Sizes.SeqΩ d → Sizes.SeqΩ d) =
        fun x c => (if fl c then (fun y : ℝ => -y) else (fun y : ℝ => y)) (x c) := by
      funext x c
      exact he2 x c
    rw [hP, hfun]
    exact h
  refine ⟨e1.trans e2, ?_, ?_⟩
  · have hm1 : MeasurePreserving e1 (Sizes.seqP d) (Sizes.seqP d) := ⟨e1.measurable, h1⟩
    have hm2 : MeasurePreserving e2 (Sizes.seqP d) (Sizes.seqP d) := ⟨e2.measurable, h2⟩
    rw [MeasurableEquiv.coe_trans]
    exact hm2.comp hm1
  · intro m ω
    funext c
    have h3 : (e1.trans e2) ω ⟨m, c⟩ =
        (if fl ⟨m, c⟩ then (fun y : ℝ => -y) else (fun y : ℝ => y)) (ω (Ψ ⟨m, c⟩)) := by
      rw [MeasurableEquiv.coe_trans]
      change e2 (e1 ω) ⟨m, c⟩ = _
      rw [he2, he1]
    change (e1.trans e2) ω ⟨m, c⟩ = MLExpInv_Phi (φ m) (Sizes.slice d m ω) c
    rw [h3]
    unfold MLExpInv_Phi
    by_cases hc : MLExpInv_flip (φ m) c
    · have hc' : fl ⟨m, c⟩ := hc
      simp only [hc, hc', ite_true]
      rfl
    · have hc' : ¬ fl ⟨m, c⟩ := hc
      simp only [hc, hc', ite_false]
      rfl

/-- The expectation of a matrix functional along `seqHflow` is unchanged by the relabelling:
if `F(M_{φ,φ}) = F'(M)` for every `M`, then `𝔼F'(H_u) = 𝔼F(H_u)`. -/
private theorem MLExpInv_integral_eq (n : ℕ) (u : ℝ) {T : Z2 (d.L n) ≃ Z2 (d.L n)}
    (hT : MLExpInv_Aut T)
    (F F' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (hF : ∀ M, F (M.submatrix (MLExpInv_phi (d.W n) T) (MLExpInv_phi (d.W n) T)) = F' M) :
    ∫ ω, F' (Sizes.seqHflow d n u ω) ∂(Sizes.seqP d) =
      ∫ ω, F (Sizes.seqHflow d n u ω) ∂(Sizes.seqP d) := by
  classical
  obtain ⟨Tf, hTf, hTn⟩ : ∃ Tf : ∀ m, Z2 (d.L m) ≃ Z2 (d.L m),
      (∀ m, MLExpInv_Aut (Tf m)) ∧ Tf n = T := by
    let f0 : ∀ m, Z2 (d.L m) ≃ Z2 (d.L m) := fun m => Equiv.refl _
    refine ⟨Function.update f0 n T, fun m => ?_, Function.update_self n T f0⟩
    by_cases h : m = n
    · subst h
      rw [Function.update_self]; exact hT
    · rw [Function.update_of_ne h]; exact MLExpInv_Aut_refl
  obtain ⟨Φ, hΦ, hsl⟩ := MLExpInv_seq d (fun m => MLExpInv_phi (d.W m) (Tf m))
    (fun m => MLExpInv_svar_phi (d.W m) (hTf m))
  have hH : ∀ ω, Sizes.seqHflow d n u (Φ ω) =
      (Sizes.seqHflow d n u ω).submatrix (MLExpInv_phi (d.W n) T) (MLExpInv_phi (d.W n) T) := by
    intro ω
    unfold Sizes.seqHflow Hflow
    rw [hsl, MLExpInv_Xmat]
    simp only [hTn]
    rfl
  calc ∫ ω, F' (Sizes.seqHflow d n u ω) ∂(Sizes.seqP d)
      = ∫ ω, F ((Sizes.seqHflow d n u ω).submatrix (MLExpInv_phi (d.W n) T)
          (MLExpInv_phi (d.W n) T)) ∂(Sizes.seqP d) := by
        simp_rw [hF]
    _ = ∫ ω, F (Sizes.seqHflow d n u (Φ ω)) ∂(Sizes.seqP d) := by
        simp_rw [hH]
    _ = ∫ ω, F (Sizes.seqHflow d n u ω) ∂(Sizes.seqP d) :=
        hΦ.integral_comp' (fun ω => F (Sizes.seqHflow d n u ω))

end Seq

/-! ## 5. The drift terms at `n = 2` are equivariant -/

section Drift

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `Σ_{x,y} A_x S^{(B)}_{xy} B_y`. -/
private def MLExpInv_sbSum (A B : Z2 L → ℂ) : ℂ := ∑ x : Z2 L, ∑ y : Z2 L, A x * SB L x y * B y

/-- `𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}` at length 2: the single cut `(k,l') = (1,2)`, two loops of length 2
(the same identity as the private `MLExpDrift_elklkN_two`, `Evolution/MLExpDrift.lean`). -/
private theorem MLExpInv_elklkN_two (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    elklkN L W E u M (loopOf σ a) =
      (W : ℂ) ^ 2 * MLExpInv_sbSum (fun x => LKf L W E u M (loopOf σ ![x, a 1]))
        (fun y => LKf L W E u M (loopOf σ ![a 0, y])) := by
  have hlen : (loopOf σ a).length = 2 := by simp [loopOf, LoopIdx.length]
  unfold elklkN MLExpInv_sbSum
  rw [hlen]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  have h2 : Finset.Ioc 1 2 = {2} := by decide
  have h3 : Finset.Ioc 2 2 = ∅ := by decide
  rw [h1, Finset.sum_pair (by norm_num), h2, h3]
  simp only [Finset.sum_singleton, Finset.sum_empty, add_zero]
  rfl

/-- `𝓔^{(G̃)}` at length 2: the cuts `k = 1, 2`, a 1-loop times a 3-loop (the same identity as the
private `MLExpDrift_egtN_two`, `Evolution/MLExpDrift.lean`). -/
private theorem MLExpInv_egtN_two (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    egtN L W E u M (loopOf σ a) =
      (W : ℂ) ^ 2 * (MLExpInv_sbSum (fun x => avgErr L W E u M (σ 0) x)
          (fun y => LLf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) +
        MLExpInv_sbSum (fun x => avgErr L W E u M (σ 1) x)
          (fun y => LLf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1]))) := by
  have hlen : (loopOf σ a).length = 2 := by simp [loopOf, LoopIdx.length]
  unfold egtN MLExpInv_sbSum
  rw [hlen]
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by norm_num)]
  rw [← Finset.sum_add_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rfl

/-- The window sum is invariant under an automorphism of `S^{(B)}` acting on both variables. -/
private theorem MLExpInv_sbSum_comp {T : Z2 L ≃ Z2 L} (hT : MLExpInv_Aut T) (A B : Z2 L → ℂ) :
    MLExpInv_sbSum (fun x => A (T x)) (fun y => B (T y)) = MLExpInv_sbSum A B := by
  unfold MLExpInv_sbSum
  calc ∑ x, ∑ y, A (T x) * SB L x y * B (T y)
      = ∑ x, ∑ y, A (T x) * SB L (T x) (T y) * B (T y) := by
        simp_rw [MLExpInv_SB_apply hT]
    _ = ∑ x, ∑ y, A x * SB L x y * B y := by
        rw [← Equiv.sum_comp T (fun x => ∑ y, A x * SB L x y * B y)]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        exact Equiv.sum_comp T (fun y => A (T x) * SB L (T x) y * B y)

/-- **The drift integrand is equivariant**: `(𝓔^{LK×LK} + 𝓔^{(G̃)})_{u,σ,a}(M_{φ,φ}) =
(𝓔^{LK×LK} + 𝓔^{(G̃)})_{u,σ,Ta}(M)`. -/
private theorem MLExpInv_drift (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_Aut T) {E u : ℝ}
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Z2 L) :
    elklkN L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T)) (loopOf σ a) +
        egtN L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T)) (loopOf σ a) =
      elklkN L W E u M (loopOf σ (fun i => T (a i))) +
        egtN L W E u M (loopOf σ (fun i => T (a i))) := by
  have hA : (fun x => LKf L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T))
      (loopOf σ ![x, a 1])) =
      fun x => (fun x' => LKf L W E u M (loopOf σ ![x', T (a 1)])) (T x) := by
    funext x
    rw [MLExpInv_LKf W hL hT hE hu0 hu1]
    congr 2
    funext i; fin_cases i <;> rfl
  have hB : (fun y => LKf L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T))
      (loopOf σ ![a 0, y])) =
      fun y => (fun y' => LKf L W E u M (loopOf σ ![T (a 0), y'])) (T y) := by
    funext y
    rw [MLExpInv_LKf W hL hT hE hu0 hu1]
    congr 2
    funext i; fin_cases i <;> rfl
  have hA1 : (fun x => avgErr L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T))
      (σ 0) x) = fun x => (fun x' => avgErr L W E u M (σ 0) x') (T x) := by
    funext x
    exact MLExpInv_avgErr W T E u M (σ 0) x
  have hB1 : (fun y => LLf L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T))
      (loopOf ![σ 0, σ 0, σ 1] ![y, a 0, a 1])) =
      fun y => (fun y' => LLf L W E u M (loopOf ![σ 0, σ 0, σ 1]
        ![y', T (a 0), T (a 1)])) (T y) := by
    funext y
    rw [MLExpInv_LLf]
    congr 2
    funext i; fin_cases i <;> rfl
  have hA2 : (fun x => avgErr L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T))
      (σ 1) x) = fun x => (fun x' => avgErr L W E u M (σ 1) x') (T x) := by
    funext x
    exact MLExpInv_avgErr W T E u M (σ 1) x
  have hB2 : (fun y => LLf L W E u (M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T))
      (loopOf ![σ 0, σ 1, σ 1] ![a 0, y, a 1])) =
      fun y => (fun y' => LLf L W E u M (loopOf ![σ 0, σ 1, σ 1]
        ![T (a 0), y', T (a 1)])) (T y) := by
    funext y
    rw [MLExpInv_LLf]
    congr 2
    funext i; fin_cases i <;> rfl
  have s1 := MLExpInv_sbSum_comp hT (fun x' => LKf L W E u M (loopOf σ ![x', T (a 1)]))
    (fun y' => LKf L W E u M (loopOf σ ![T (a 0), y']))
  have s2 := MLExpInv_sbSum_comp hT (fun x' => avgErr L W E u M (σ 0) x')
    (fun y' => LLf L W E u M (loopOf ![σ 0, σ 0, σ 1] ![y', T (a 0), T (a 1)]))
  have s3 := MLExpInv_sbSum_comp hT (fun x' => avgErr L W E u M (σ 1) x')
    (fun y' => LLf L W E u M (loopOf ![σ 0, σ 1, σ 1] ![T (a 0), y', T (a 1)]))
  rw [MLExpInv_elklkN_two, MLExpInv_egtN_two, MLExpInv_elklkN_two, MLExpInv_egtN_two]
  rw [hA, hB, hA1, hB1, hA2, hB2]
  beta_reduce
  rw [s1, s2, s3]

end Drift

/-! ## 6. The statement -/

section Main

variable (d : Sizes)

/-- `f_{u,σ} = 𝔼(𝓛-𝒦)_{u,σ}` is invariant under `a ↦ Ta` for every automorphism `T` of `S^{(B)}`. -/
private theorem MLExpInv_expErrT (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) {T : Z2 (d.L n) ≃ Z2 (d.L n)} (hT : MLExpInv_Aut T)
    (a : Fin 2 → Z2 (d.L n)) :
    expErrT d n E u σ (fun i => T (a i)) = expErrT d n E u σ a := by
  unfold expErrT expLoopErr
  have hK : KLoop.Kcal (d.L n) (d.W n) E u (loopOf σ (fun i => T (a i))) =
      KLoop.Kcal (d.L n) (d.W n) E u (loopOf σ a) :=
    MLExpInv_Kcal_two (d.three_le_L n) hT (d.W n) hE hu0 hu1 (σ 0) (σ 1) (a 0) (a 1)
  have hI := MLExpInv_integral_eq d n u hT
    (fun M => LLf (d.L n) (d.W n) E u M (loopOf σ a))
    (fun M => LLf (d.L n) (d.W n) E u M (loopOf σ (fun i => T (a i))))
    (fun M => MLExpInv_LLf (d.W n) T E u M σ a)
  rw [hK]
  exact congrArg (fun z => z - KLoop.Kcal (d.L n) (d.W n) E u (loopOf σ a)) hI

/-- `D_{u,σ} = 𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)})_{u,σ}` is invariant under `a ↦ Ta` for every automorphism `T`
of `S^{(B)}`. -/
private theorem MLExpInv_expDriftT (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) {T : Z2 (d.L n) ≃ Z2 (d.L n)} (hT : MLExpInv_Aut T)
    (a : Fin 2 → Z2 (d.L n)) :
    expDriftT d n E u σ (fun i => T (a i)) = expDriftT d n E u σ a := by
  unfold expDriftT
  exact MLExpInv_integral_eq d n u hT
    (fun M => elklkN (d.L n) (d.W n) E u M (loopOf σ a) + egtN (d.L n) (d.W n) E u M (loopOf σ a))
    (fun M => elklkN (d.L n) (d.W n) E u M (loopOf σ (fun i => T (a i))) +
      egtN (d.L n) (d.W n) E u M (loopOf σ (fun i => T (a i))))
    (fun M => MLExpInv_drift (d.three_le_L n) hT hE hu0 hu1 M σ a)

/-- **`ExpInvariant`** (`Evolution/MLExpVocab.lean`), proved: the expected
tensors `f_{u,σ} = 𝔼(𝓛-𝒦)_{u,σ}` and `D_{u,σ} = 𝔼(𝓔^{LK×LK} + 𝓔^{(G̃)})_{u,σ}` are invariant under all
translations and under the negation of the labels.  The input behind (`eq:case4_B`),
which the paper asserts without proof.  Proof: the lattice automorphisms `a ↦ a + v`, `a ↦ -a` of
`Z_L²` preserve `S^{(B)}` (hence `Θ_ξ` and `𝒦`, `Kcal_two`), and induce bijections of the fine lattice
preserving the variance profile `S_{ij}`; the coordinate map with sign flips is a measure-preserving
equivalence of the Gaussian sample space (`Xentry` is oriented by `idxKey`, so pairs whose
orientation is reversed are swapped and their imaginary coordinate changes sign), with
`X(Φω) = X(ω)_{φ,φ}`; the integrands are equivariant (`Gsig`, `Eblk`, `Kcal_two`, the window sums). -/
theorem expInvariant : ExpInvariant d := by
  intro n E u hE hu0 hu1 σ
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro v a
    exact MLExpInv_expErrT d n hE hu0 hu1 σ (MLExpInv_Aut_addRight v) a
  · intro a
    exact MLExpInv_expErrT d n hE hu0 hu1 σ MLExpInv_Aut_neg a
  · intro v a
    exact MLExpInv_expDriftT d n hE hu0 hu1 σ (MLExpInv_Aut_addRight v) a
  · intro a
    exact MLExpInv_expDriftT d n hE hu0 hu1 σ MLExpInv_Aut_neg a

end Main

end RBM.Evol

/-! ## 8. Public restatements of the automorphism machinery

The private lemmas above serve the tensors of `k = 2`.  The general-`k` argument of
`Induction/AltSymm.lean` (`altExpSymm`) needs the same facts about `S^{(B)}`, `Θ_ξ`, the
relabelling of the fine lattice and the change of variables in the Gaussian sample space, for loops of
every length.  Every declaration below restates the private lemma of the same stem (no proof is
recopied); the relabelled matrix `M_{φ,φ}` is exposed as `MLExpInv_relabel`, and the loop-level
identities are stated for an arbitrary loop index `I` (`I.a` mapped by `T`). -/

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind

section Public

/-- A bijection of `Z_L²` preserving the five-point relation of `S^{(B)}` (public form of
`MLExpInv_Aut`). -/
def MLExpInv_IsAut {L : ℕ} [NeZero L] (T : Z2 L ≃ Z2 L) : Prop :=
  ∀ a b : Z2 L, T a - T b ∈ sbSupport L ↔ a - b ∈ sbSupport L

theorem MLExpInv_IsAut_addRight {L : ℕ} [NeZero L] (v : Z2 L) :
    MLExpInv_IsAut (Equiv.addRight v) :=
  MLExpInv_Aut_addRight v

theorem MLExpInv_IsAut_neg {L : ℕ} [NeZero L] : MLExpInv_IsAut (Equiv.neg (Z2 L)) :=
  MLExpInv_Aut_neg

theorem MLExpInv_IsAut_SB {L : ℕ} [NeZero L] {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T)
    (a b : Z2 L) : SB L (T a) (T b) = SB L a b :=
  MLExpInv_SB_apply hT a b

theorem MLExpInv_IsAut_Theta {L : ℕ} [NeZero L] (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L}
    (hT : MLExpInv_IsAut T) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    Theta L ξ (T a) (T b) = Theta L ξ a b :=
  MLExpInv_Theta_apply hL hT hξ a b

/-- `‖t m(s) m(s')‖ = t` for `|E| ≤ 2`, `0 ≤ t` (public form of `MLExpInv_norm_xi`): the propagator
arguments `ξ = t m m'` of `𝒦`, `ϴ` have norm `t < 1`. -/
theorem MLExpInv_xi_norm {E t : ℝ} (hE : |E| ≤ 2) (ht : 0 ≤ t) (s s' : Bool) :
    ‖(t : ℂ) * (KLoop.mSig E s * KLoop.mSig E s')‖ = t :=
  MLExpInv_norm_xi hE ht s s'

/-- The relabelled matrix `M_{φ,φ}` of the fine lattice (`φ` moves the block label by `T` and keeps
the offset). -/
def MLExpInv_relabel {L : ℕ} [NeZero L] (W : ℕ) [NeZero W] (T : Z2 L ≃ Z2 L)
    (M : Matrix (Idx L W) (Idx L W) ℂ) : Matrix (Idx L W) (Idx L W) ℂ :=
  M.submatrix (MLExpInv_phi W T) (MLExpInv_phi W T)

/-- `𝓛_{u,I}(M_{φ,φ}) = 𝓛_{u,T·I}(M)` for every loop index `I` (`T·I` moves the labels). -/
theorem MLExpInv_relabel_LLf {L : ℕ} [NeZero L] (W : ℕ) [NeZero W] (T : Z2 L ≃ Z2 L) (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) :
    LLf L W E u (MLExpInv_relabel W T M) I = LLf L W E u M ⟨I.σ, I.a.map T⟩ := by
  unfold LLf MLExpInv_relabel
  rw [MLExpInv_blockMat_submatrix, MLExpInv_gloop_submatrix]

/-- `⟨(G - m) E_x⟩` at the relabelled matrix. -/
theorem MLExpInv_relabel_avgErr {L : ℕ} [NeZero L] (W : ℕ) [NeZero W] (T : Z2 L ≃ Z2 L)
    (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (s : Bool) (x : Z2 L) :
    avgErr L W E u (MLExpInv_relabel W T M) s x = avgErr L W E u M s (T x) :=
  MLExpInv_avgErr W T E u M s x

/-- **The change of variables** (public form of `MLExpInv_integral_eq`): if
`F(M_{φ,φ}) = F'(M)` for every matrix `M`, then `𝔼F'(H_u) = 𝔼F(H_u)` (no integrability needed). -/
theorem MLExpInv_relabel_integral (d : Sizes) (n : ℕ) (u : ℝ) {T : Z2 (d.L n) ≃ Z2 (d.L n)}
    (hT : MLExpInv_IsAut T)
    (F F' : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ)
    (hF : ∀ M, F (MLExpInv_relabel (d.W n) T M) = F' M) :
    ∫ ω, F' (Sizes.seqHflow d n u ω) ∂(Sizes.seqP d) =
      ∫ ω, F (Sizes.seqHflow d n u ω) ∂(Sizes.seqP d) :=
  MLExpInv_integral_eq d n u hT F F' hF

end Public

end RBM.Evol
