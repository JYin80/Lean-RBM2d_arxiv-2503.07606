/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.MLExpInv
import RBM2D.Induction.StoppedEndDefs

/-!
# Translation and negation invariance of `𝒬_u 𝔼 B_m` for alternating `σ` of every length

The statement `AltExpSymm` (`RBM2D.Induction.StoppedEndDefs`); paper: `eq:case4_B`, asserted
there without proof.

**Result** (namespace `RBM.Ind`, `variable (d : Sizes)`): `altExpSymm : AltExpSymm d`: for every
`n`, `|E| < 2`, `0 ≤ u < 1`, `k ≥ 2`, alternating `σ` and `m = 0..5`, the
deterministic tensor `𝒬_u 𝔼 B_m(H_u)` (`altB`, `Qop`) is invariant under every translation and under
the negation of the `k` labels (`TensorInvariantK`).  Deterministic, finite size; no hypothesis
beyond the statement, no external input.  (The proof uses neither the alternation of `σ` nor
`k ≥ 2`; both are in the statement.)

Proof (the general-`k` extension of the argument of `RBM2D.Evolution.MLExpInv`; the one-dimensional
argument has no Case 4).  The private machinery of `MLExpInv` is reached through the public
restatements in its last section (`MLExpInv_IsAut`, `MLExpInv_relabel`, `MLExpInv_relabel_LLf`,
`MLExpInv_relabel_integral`, ...).
1. Section 1: `𝒦` at *every* length is invariant under `a ↦ T ∘ a` (`AltSymm_Kcal_map`): length `1` has
   no label, length `2` is `(Kn2sol)`, length `n ≥ 3` is the tree sum `Kn`, whose value `treeValW`
   is a sum over the labels of the internal nodes; substituting the internal labels `b = T ∘ b'`
   and using `Θ_ξ(Tx,Ty) = Θ_ξ(x,y)`, `1(Tx,Ty) = 1(x,y)` gives the claim (the argument of
   `MLExpInv` uses `Kcal_two` only).  No well-formedness of the loop index
   is needed.
2. Section 2: the label relabelling `I ↦ ⟨I.σ, I.a.map T⟩` of a loop index commutes with `loopOf` and with
   the cut operations `cutGlueL`, `cutGlueR`, `cutGlue` (`List.map_take`, `List.map_drop`); hence
   `(𝓛-𝒦)`, the cut sums `ksimLK`, `elklkN`, `egtN` at the relabelled matrix `M_{φ,φ}` equal the
   same at `M` and the relabelled loop (`Σ_{a,b ∈ Z_L²}` reindexed by `(a,b) ↦ (Ta,Tb)`,
   `SB(Ta,Tb) = SB(a,b)`).
3. Section 3: `𝒫`, `ϑ`, `ϑ̇`, `𝒬`, `ϴ` commute with the relabelling of the labels of a `k`-tensor;
   `ϑ̇` is a derivative at `u ∈ [0,1)`, and `ϑ_{v,T·} = ϑ_{v,·}` holds on the whole neighbourhood
   `(-1,1)`.
4. Section 4: `B_m(M_{φ,φ}) = B_m(M) ∘ T` for `m = 0..5`.
5. Section 5: the change of variables (`MLExpInv_relabel_integral`, measure-preserving `Φ`) gives
   `𝔼B_m(H_u) ∘ T = 𝔼B_m(H_u)`, and `𝒬_u` commutes with `T`; `altExpSymm`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. `𝒦` at every length is invariant under the relabelling of the labels -/

section Kcal

variable {L : ℕ} [NeZero L]

/-- The value of a tree is unchanged when the leaf labels are moved by `T`, if every edge weight is. -/
private theorem AltSymm_treeValW_comp {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n))
    (T : Z2 L ≃ Z2 L) (a : Fin n → Z2 L) (M : Fin n → Matrix (Z2 L) (Z2 L) ℂ)
    (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ)
    (hM : ∀ v x y, M v (T x) (T y) = M v x y) (hE : ∀ d x y, E d (T x) (T y) = E d x y) :
    KLoop.treeValW L F (fun i => T (a i)) M E = KLoop.treeValW L F a M E := by
  unfold KLoop.treeValW
  refine (Fintype.sum_equiv (Equiv.piCongrRight fun _ : ↥(KLoop.nodes F) => T) _ _
    (fun b => ?_)).symm
  simp only [Equiv.piCongrRight_apply, Pi.map_apply, hM, hE]

/-- `Kn` (the tree sum, `n ≥ 1`) is invariant under an automorphism `T` of `S^{(B)}`. -/
private theorem AltSymm_Kn_comp (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) (W : ℕ)
    {E t : ℝ} (hE : |E| ≤ 2) (ht0 : 0 ≤ t) (ht1 : t < 1) {n : ℕ} [NeZero n] (σ : Fin n → Bool)
    (a : Fin n → Z2 L) :
    KLoop.Kn L W (KLoop.mSig E) t n σ (fun i => T (a i)) = KLoop.Kn L W (KLoop.mSig E) t n σ a := by
  have hξ : ∀ s s' : Bool, ‖(t : ℂ) * (KLoop.mSig E s * KLoop.mSig E s')‖ < 1 := fun s s' => by
    rw [MLExpInv_xi_norm hE ht0]; exact ht1
  unfold KLoop.Kn
  congr 1
  refine Finset.sum_congr rfl fun F _ => ?_
  unfold KLoop.treeValG
  refine AltSymm_treeValW_comp F T a _ _ (fun v x y => ?_) (fun d x y => ?_)
  · exact MLExpInv_IsAut_Theta hL hT (hξ _ _) x y
  · simp only [KLoop.thetaEdge, Matrix.sub_apply, MLExpInv_IsAut_Theta hL hT (hξ _ _)]
    have : (1 : Matrix (Z2 L) (Z2 L) ℂ) (T x) (T y) = (1 : Matrix (Z2 L) (Z2 L) ℂ) x y := by
      simp only [Matrix.one_apply, T.apply_eq_iff_eq]
    rw [this]

/-- `𝒦` at every loop length is invariant under the relabelling `I.a ↦ T ∘ I.a` of the labels
(the tree sum `Kn` for length `≥ 3`, `(Kn2sol)` for length `2`, `m(σ₁)` for length `1`); no
well-formedness of `I` is needed (`𝒦` reads only `I.length = I.a.length` labels). -/
private theorem AltSymm_Kcal_map (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) (W : ℕ)
    {E t : ℝ} (hE : |E| ≤ 2) (ht0 : 0 ≤ t) (ht1 : t < 1) (I : LoopIdx (Z2 L)) :
    KLoop.Kcal L W E t ⟨I.σ, I.a.map T⟩ = KLoop.Kcal L W E t I := by
  have hξ : ∀ s s' : Bool, ‖(t : ℂ) * (KLoop.mSig E s * KLoop.mSig E s')‖ < 1 := fun s s' => by
    rw [MLExpInv_xi_norm hE ht0]; exact ht1
  have hlen : (⟨I.σ, I.a.map T⟩ : LoopIdx (Z2 L)).length = I.length := List.length_map _
  have hget : ∀ i, i < I.a.length → (I.a.map T).getD i 0 = T (I.a.getD i 0) := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  unfold KLoop.Kcal KLoop.Kgen
  simp only [hlen]
  by_cases h1 : I.length = 1
  · simp only [↓reduceIte, h1]
  · by_cases h2 : I.length = 2
    · have h0 : 0 < I.a.length := by have : I.length = I.a.length := rfl; omega
      have h1' : 1 < I.a.length := by have : I.length = I.a.length := rfl; omega
      simp only [h2, ↓reduceIte]
      unfold KLoop.kTwo
      simp only [hget 0 h0, hget 1 h1', MLExpInv_IsAut_Theta hL hT (hξ _ _)]
    · by_cases h3 : 3 ≤ I.length
      · simp only [h1, h2, h3, ↓reduceIte, ↓reduceDIte]
        have hne : NeZero I.length := ⟨by omega⟩
        have hK : ∀ (n' : ℕ) (hnz : NeZero n') (hn' : n' = I.length) (a' : Fin n' → Z2 L),
            (∀ i : Fin n', a' i = T (I.a.getD i 0)) →
            KLoop.Kn L W (KLoop.mSig E) t n' (fun i => I.σ.getD i false) a' =
              KLoop.Kn L W (KLoop.mSig E) t I.length (fun i => I.σ.getD i false)
                (fun i => I.a.getD i 0) := by
          intro n' hnz hn' a' ha
          subst hn'
          have : a' = fun i : Fin I.length => T (I.a.getD i 0) := funext ha
          rw [this]
          exact AltSymm_Kn_comp hL hT W hE ht0 ht1 _ _
        refine hK _ ⟨by rw [hlen]; omega⟩ hlen _ (fun i => ?_)
        exact hget i (by have := i.isLt; simpa [LoopIdx.length] using this)
      · simp only [h1, h2, h3, ↓reduceIte, ↓reduceDIte]

end Kcal

/-! ## 2. The relabelling of a loop index, the cut operations and the matrix-level hierarchy terms -/

section Loops

variable {L : ℕ} [NeZero L] (W : ℕ) [NeZero W]

/-- The relabelling `I.a ↦ T ∘ I.a` of the block labels of a loop index. -/
private def AltSymm_mapT (T : Z2 L ≃ Z2 L) (I : LoopIdx (Z2 L)) : LoopIdx (Z2 L) :=
  ⟨I.σ, I.a.map T⟩

private theorem AltSymm_mapT_length (T : Z2 L ≃ Z2 L) (I : LoopIdx (Z2 L)) :
    (AltSymm_mapT T I).length = I.length := List.length_map _

private theorem AltSymm_mapT_loopOf {k : ℕ} (T : Z2 L ≃ Z2 L) (σ : Fin k → Bool)
    (b : Fin k → Z2 L) :
    AltSymm_mapT T (loopOf σ b) = loopOf σ (fun i => T (b i)) := by
  simp only [AltSymm_mapT, loopOf, List.map_ofFn]
  rfl

private theorem AltSymm_mapT_cutGlueL (T : Z2 L ≃ Z2 L) (I : LoopIdx (Z2 L)) (k l : ℕ) (b : Z2 L) :
    (AltSymm_mapT T I).cutGlueL k l (T b) = AltSymm_mapT T (I.cutGlueL k l b) := by
  simp [AltSymm_mapT, LoopIdx.cutGlueL, List.map_take, List.map_drop]

private theorem AltSymm_mapT_cutGlueR (T : Z2 L ≃ Z2 L) (I : LoopIdx (Z2 L)) (k l : ℕ) (b : Z2 L) :
    (AltSymm_mapT T I).cutGlueR k l (T b) = AltSymm_mapT T (I.cutGlueR k l b) := by
  simp [AltSymm_mapT, LoopIdx.cutGlueR, List.map_take, List.map_drop]

private theorem AltSymm_mapT_cutGlue (T : Z2 L ≃ Z2 L) (I : LoopIdx (Z2 L)) (k : ℕ) (b : Z2 L) :
    (AltSymm_mapT T I).cutGlue k (T b) = AltSymm_mapT T (I.cutGlue k b) := by
  simp [AltSymm_mapT, LoopIdx.cutGlue, List.map_take, List.map_drop]

private theorem AltSymm_Kcal_mapT (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T)
    {E t : ℝ} (hE : |E| ≤ 2) (ht0 : 0 ≤ t) (ht1 : t < 1) (I : LoopIdx (Z2 L)) :
    KLoop.Kcal L W E t (AltSymm_mapT T I) = KLoop.Kcal L W E t I :=
  AltSymm_Kcal_map hL hT W hE ht0 ht1 I

/-- `∑_{a,b} f(Ta, Tb) = ∑_{a,b} f(a, b)`. -/
private theorem AltSymm_sum2 (T : Z2 L ≃ Z2 L) (f : Z2 L → Z2 L → ℂ) :
    ∑ a, ∑ b, f (T a) (T b) = ∑ a, ∑ b, f a b := by
  calc ∑ a, ∑ b, f (T a) (T b) = ∑ a, ∑ b, f (T a) b :=
        Finset.sum_congr rfl fun a _ => Equiv.sum_comp T (f (T a))
    _ = ∑ a, ∑ b, f a b := Equiv.sum_comp T (fun a => ∑ b, f a b)

/-- `𝓛_{u,I}(M_{φ,φ}) = 𝓛_{u,T·I}(M)`. -/
private theorem AltSymm_LLf (T : Z2 L ≃ Z2 L) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (I : LoopIdx (Z2 L)) :
    LLf L W E u (MLExpInv_relabel W T M) I = LLf L W E u M (AltSymm_mapT T I) :=
  MLExpInv_relabel_LLf W T E u M I

/-- `(𝓛-𝒦)_{u,I}(M_{φ,φ}) = (𝓛-𝒦)_{u,T·I}(M)` for every loop index (every length). -/
private theorem AltSymm_LKf (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {E u : ℝ}
    (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (I : LoopIdx (Z2 L)) :
    LKf L W E u (MLExpInv_relabel W T M) I = LKf L W E u M (AltSymm_mapT T I) := by
  unfold LKf
  rw [AltSymm_LLf, AltSymm_Kcal_mapT W hL hT hE hu0 hu1]

/-- `[𝒦 ∼ (𝓛-𝒦)]^l_{u,I}(M_{φ,φ}) = [𝒦 ∼ (𝓛-𝒦)]^l_{u,T·I}(M)`. -/
private theorem AltSymm_ksimLK (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {E u : ℝ}
    (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ) (l : ℕ)
    (I : LoopIdx (Z2 L)) :
    ksimLK L W E u (MLExpInv_relabel W T M) l I = ksimLK L W E u M l (AltSymm_mapT T I) := by
  unfold ksimLK
  rw [AltSymm_mapT_length]
  refine congrArg (fun z => (W : ℂ) ^ 2 * z) ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l' _ => ?_
  refine Eq.trans ?_ (AltSymm_sum2 T _)
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [AltSymm_mapT_cutGlueL, AltSymm_mapT_cutGlueR, AltSymm_mapT_length,
    AltSymm_LKf W hL hT hE hu0 hu1, AltSymm_Kcal_mapT W hL hT hE hu0 hu1, MLExpInv_IsAut_SB hT]

/-- `𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}_{u,I}(M_{φ,φ}) = 𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}_{u,T·I}(M)`. -/
private theorem AltSymm_elklkN (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {E u : ℝ}
    (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (I : LoopIdx (Z2 L)) :
    elklkN L W E u (MLExpInv_relabel W T M) I = elklkN L W E u M (AltSymm_mapT T I) := by
  unfold elklkN
  rw [AltSymm_mapT_length]
  refine congrArg (fun z => (W : ℂ) ^ 2 * z) ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l' _ => ?_
  refine Eq.trans ?_ (AltSymm_sum2 T _)
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [AltSymm_mapT_cutGlueL, AltSymm_mapT_cutGlueR,
    AltSymm_LKf W hL hT hE hu0 hu1, MLExpInv_IsAut_SB hT]

/-- `𝓔^{(G̃)}_{u,I}(M_{φ,φ}) = 𝓔^{(G̃)}_{u,T·I}(M)`. -/
private theorem AltSymm_egtN {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (I : LoopIdx (Z2 L)) :
    egtN L W E u (MLExpInv_relabel W T M) I = egtN L W E u M (AltSymm_mapT T I) := by
  unfold egtN
  rw [AltSymm_mapT_length]
  refine congrArg (fun z => (W : ℂ) ^ 2 * z) ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Eq.trans ?_ (AltSymm_sum2 T _)
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [AltSymm_mapT_cutGlue, MLExpInv_relabel_avgErr, AltSymm_LLf, MLExpInv_IsAut_SB hT]
  rfl

end Loops

/-! ## 3. The tensor operations `𝒫`, `ϑ`, `ϑ̇`, `𝒬`, `ϴ` commute with the relabelling of the labels -/

section Tensor

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `(A ∘ T)(a) = A(T ∘ a)`: the relabelling of a `k`-tensor. -/
private def AltSymm_tcomp (T : Z2 L ≃ Z2 L) (A : (Fin k → Z2 L) → ℂ) : (Fin k → Z2 L) → ℂ :=
  fun a => A (fun i => T (a i))

/-- `𝒫(A ∘ T)_{a₁} = (𝒫A)_{T a₁}`: `𝒫` sums over all of `(Z_L²)^k`, so the reindexing is exact. -/
private theorem AltSymm_Psum_comp (T : Z2 L ≃ Z2 L) (A : (Fin k → Z2 L) → ℂ) (a₁ : Z2 L) :
    Psum L (AltSymm_tcomp T A) a₁ = Psum L A (T a₁) := by
  unfold Psum AltSymm_tcomp
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ : Fin k => T) _ _ (fun a => ?_)
  simp only [Equiv.piCongrRight_apply, Pi.map_apply, T.apply_eq_iff_eq]
  rfl

private theorem AltSymm_vartheta (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {t : ℝ}
    (ht : |t| < 1) (a : Fin k → Z2 L) :
    vartheta L t (fun i => T (a i)) = vartheta L t a := by
  have hξ : ‖(t : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact ht
  unfold vartheta
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  exact MLExpInv_IsAut_Theta hL hT hξ (a 0) (a i)

/-- `ϑ̇_{t,Ta} = ϑ̇_{t,a}` for `0 ≤ t < 1`: the derivative at `t` is taken along the two-sided
neighbourhood `(-1,1)` on which `ϑ_{v,T·} = ϑ_{v,·}`. -/
private theorem AltSymm_varthetaDot (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → Z2 L) :
    varthetaDot L t (fun i => T (a i)) = varthetaDot L t a := by
  unfold varthetaDot
  refine Filter.EventuallyEq.deriv_eq ?_
  have hnhds : Set.Ioo (-1 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds (by linarith) ht1
  filter_upwards [hnhds] with v hv
  exact AltSymm_vartheta hL hT (abs_lt.2 hv) a

/-- `𝒬_t (A ∘ T) = (𝒬_t A) ∘ T`. -/
private theorem AltSymm_Qop (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (A : (Fin k → Z2 L) → ℂ) :
    Qop L t (AltSymm_tcomp T A) = AltSymm_tcomp T (Qop L t A) := by
  funext a
  have hab : |t| < 1 := abs_lt.2 ⟨by linarith, ht1⟩
  simp only [Qop, AltSymm_tcomp, AltSymm_Psum_comp, AltSymm_vartheta hL hT hab]

private theorem AltSymm_thetaGenMat (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {ξ : ℂ}
    {u : ℝ} (hξ : ‖(u : ℂ) * ξ‖ < 1) (x y : Z2 L) :
    thetaGenMat L ξ u (T x) (T y) = thetaGenMat L ξ u x y := by
  unfold thetaGenMat
  simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  refine congrArg (fun z => ξ * z) ?_
  refine (Equiv.sum_comp T (fun z => SB L (T x) z * Theta L ((u : ℂ) * ξ) z (T y))).symm.trans ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [MLExpInv_IsAut_SB hT, MLExpInv_IsAut_Theta hL hT hξ]

/-- `ϴ_{u,σ} (A ∘ T) = (ϴ_{u,σ} A) ∘ T` (`ξ_i S Θ_{uξ_i}` is invariant, `update (T a) i (T b) = T (update a i b)`). -/
private theorem AltSymm_thetaSig (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {E u : ℝ}
    (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin k → Bool)
    (A : (Fin k → Z2 L) → ℂ) :
    thetaSig L E σ u (AltSymm_tcomp T A) = AltSymm_tcomp T (thetaSig L E σ u A) := by
  funext a
  unfold thetaSig AltSymm_tcomp
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv T _ _ (fun b => ?_)
  have hξ : ‖(u : ℂ) * (KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)))‖ < 1 := by
    rw [MLExpInv_xi_norm hE hu0]; exact hu1
  rw [AltSymm_thetaGenMat hL hT hξ]
  have hupd : (fun j => T (Function.update a i b j)) =
      Function.update (fun j => T (a j)) i (T b) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hupd]

end Tensor

/-! ## 4. The six tensors `B₀, …, B₅` are equivariant, and so is `𝒬_u 𝔼 B_m` -/

section Hier

variable {L : ℕ} [NeZero L] (W : ℕ) [NeZero W] {k : ℕ} [NeZero k]

private theorem AltSymm_lkTensor (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {E u : ℝ}
    (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin k → Bool) :
    lkTensor L W E u (MLExpInv_relabel W T M) σ = AltSymm_tcomp T (lkTensor L W E u M σ) := by
  funext b
  unfold lkTensor AltSymm_tcomp
  rw [AltSymm_LKf W hL hT hE hu0 hu1, AltSymm_mapT_loopOf]

/-- **`B_m(M_{φ,φ}) = B_m(M) ∘ T` for `m = 0..5`, every `σ`, every length `k`.** -/
private theorem AltSymm_altB (hL : 3 ≤ L) {T : Z2 L ≃ Z2 L} (hT : MLExpInv_IsAut T) {E u : ℝ}
    (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (σ : Fin k → Bool) (m : Fin 6) :
    altB L W E u (MLExpInv_relabel W T M) σ m = AltSymm_tcomp T (altB L W E u M σ m) := by
  have hab : |u| < 1 := abs_lt.2 ⟨by linarith, hu1⟩
  have hlk := AltSymm_lkTensor W hL hT hE hu0 hu1 M σ
  fin_cases m
  · exact hlk
  · funext a
    simp only [altB, AltSymm_tcomp]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [AltSymm_ksimLK W hL hT hE hu0 hu1, AltSymm_mapT_loopOf]
  · funext a
    simp only [altB, AltSymm_tcomp]
    rw [AltSymm_elklkN W hL hT hE hu0 hu1, AltSymm_mapT_loopOf]
  · funext a
    simp only [altB, AltSymm_tcomp]
    rw [AltSymm_egtN W hT, AltSymm_mapT_loopOf]
  · funext a
    simp only [altB, B4, hlk, AltSymm_thetaSig hL hT hE hu0 hu1, AltSymm_Qop hL hT hu0 hu1]
    rfl
  · funext a
    simp only [altB, B5, hlk, AltSymm_Psum_comp, AltSymm_tcomp, AltSymm_varthetaDot hL hT hu0 hu1]

end Hier

/-! ## 5. The result -/

section Main

variable (d : Sizes)

/-- `𝔼 B_m(H_u)` is invariant under `a ↦ T ∘ a` for every automorphism `T` of `S^{(B)}`: the change of
variables `MLExpInv_relabel_integral` (measure-preserving `Φ` of the Gaussian sample space with
`H_u(Φω) = H_u(ω)_{φ,φ}`) together with `B_m(M_{φ,φ}) = B_m(M) ∘ T`. -/
private theorem AltSymm_expect_tcomp (n : ℕ) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {k : ℕ} [NeZero k] (σ : Fin k → Bool) (m : Fin 6) {T : Z2 (d.L n) ≃ Z2 (d.L n)}
    (hT : MLExpInv_IsAut T) :
    AltSymm_tcomp T (fun b => ∫ ω, altB (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) σ m b
        ∂(Sizes.seqP d)) =
      fun b => ∫ ω, altB (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) σ m b ∂(Sizes.seqP d) := by
  funext b
  exact MLExpInv_relabel_integral d n u hT
    (fun M => altB (d.L n) (d.W n) E u M σ m b)
    (fun M => altB (d.L n) (d.W n) E u M σ m (fun i => T (b i)))
    (fun M => congrFun (AltSymm_altB (d.W n) (d.three_le_L n) hT hE hu0 hu1 M σ m) b)

/-- The core statement, for every sign vector `σ` and every length `k` (the alternation of `σ` and
`k ≥ 2` are not used): `𝒬_u 𝔼 B_m` is invariant under all translations and under the negation. -/
private theorem AltSymm_core (n : ℕ) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {k : ℕ} [NeZero k] (σ : Fin k → Bool) (m : Fin 6) :
    TensorInvariantK (Qop (d.L n) u (fun b =>
      ∫ ω, altB (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) σ m b ∂(Sizes.seqP d))) := by
  have key : ∀ {T : Z2 (d.L n) ≃ Z2 (d.L n)}, MLExpInv_IsAut T →
      AltSymm_tcomp T (Qop (d.L n) u (fun b =>
        ∫ ω, altB (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) σ m b ∂(Sizes.seqP d))) =
      Qop (d.L n) u (fun b =>
        ∫ ω, altB (d.L n) (d.W n) E u (Sizes.seqHflow d n u ω) σ m b ∂(Sizes.seqP d)) := by
    intro T hT
    rw [← AltSymm_Qop (d.three_le_L n) hT hu0 hu1, AltSymm_expect_tcomp d n hE hu0 hu1 σ m hT]
  exact ⟨fun v a => congrFun (key (MLExpInv_IsAut_addRight v)) a,
    fun a => congrFun (key MLExpInv_IsAut_neg) a⟩

/-- **`AltExpSymm`, proved** (`eq:case4_B`, asserted in the paper without proof): for every `n`, `|E| < 2`,
`0 ≤ u < 1`, every length `k ≥ 2`, every alternating `σ` and `m = 0..5`, the deterministic tensor
`𝒬_u 𝔼 B_m` is invariant under all translations `a ↦ a + v` and under the negation `a ↦ -a` of the
labels.  Proof: the lattice automorphisms `T` of `Z_L²` preserve `S^{(B)}`, hence `Θ_ξ`, `𝒦` (all
lengths, the tree representation), `ϑ_u`, `ϑ̇_u`; they induce a bijection of the fine lattice and a
measure-preserving map of the Gaussian sample space with `H_u(Φω) = H_u(ω)_{φ,φ}`
(`MLExpInv_relabel_integral`); each `B_m` is equivariant, `B_m(M_{φ,φ}) = B_m(M) ∘ T`; and `𝒬_u`
commutes with `T`. -/
theorem altExpSymm : AltExpSymm d := by
  intro n E u hE hu0 hu1 k _ hk σ _ m
  exact AltSymm_core d n hE.le hu0 hu1 σ m

end Main

end RBM.Ind
