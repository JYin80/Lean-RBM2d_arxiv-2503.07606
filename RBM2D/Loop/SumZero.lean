/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.Kcal

/-!
# The closed form of fully summed trees, and the sum-zero bound given `Q(1) = 0`

Paper: `(SZjadljsk)`, from [YY_25] Lemma 3.10 (2), §3.4.

The proof follows the one-dimensional formalization: `sum_out`, `treeZ`, `treeZ_peel`,
`treeZ_eq`, `sum_selfW`, `edgeR`, `Qlayer`, `Alayer`, `SumZero_sum_Theta_col`,
`sum_Theta_sub_one_col`, `SumZero_sum_Kpi_eq`, `sum_SigmaPi`, `sum_Kpi_closed`,
`SumZero_SigmaPi_add_const`.
Changes for `d = 2`: `ZMod L ↦ Z2 L`; `L ↦ L²` in the closed forms (`|Z_L²| = L²`);
the hypothesis `IsTSP F` becomes `F ∈ TSP n` (the laminar API of `TreeRep.lean` is private),
the peeling uses only that the parent of a diagonal is a strictly larger node, so no
hypothesis `2 ≤ n` is needed.

Specific to `d = 2`:
* the slice form `SumZero_sum_slice`: with one label `d_i = x` fixed,
  `∑_{d : d_i = x} Σ^{(π)}(t,σ,d) = Q(σ,π)`, independent of `L` and `x`
  (translation invariance plus `sum_SigmaPi`);
* `SigmaPi_alt_sumZero_le_of_Qlayer_one`: the bound `SigmaPi_alt_sumZero_le`
  under the extra hypothesis `Q(σ^{(alt)}, ∅)|_{t=1} = 0` (a conditional adapter, not the
  unconditional bound).
-/

namespace RBM.KLoop

open Finset

/-! ## 1. A light laminar API (private) -/

section LaminarLite

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem isDiag_of_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d : Fin n × Fin n} (hd : d ∈ F) : IsDiag n d.1 d.2 := by
  have h1 := mem_powerset.1 (mem_filter.1 hF).1 hd
  simpa [diagonals] using h1

omit [NeZero n] in
private theorem crossingFree_of_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) :
    CrossingFree F :=
  (mem_filter.1 hF).2

private theorem wholeP_not_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) :
    wholeP n ∉ F := by
  intro h
  have := (isDiag_of_mem_TSP hF h).2.2
  simp [wholeP] at this

/-- The parent of a diagonal of a tree is a strictly larger node. -/
private theorem nodePar_up {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d : Fin n × Fin n} (hd : d ∈ F) : ArcLe d (nodePar F d) ∧ nodePar F d ≠ d := by
  rcases minNode_mem_or (s := (nodes F).filter fun e => ArcLe d e ∧ e ≠ d) with h | h
  · exact (mem_filter.1 h).2
  · unfold nodePar
    rw [h]
    refine ⟨⟨Fin.zero_le _, ?_⟩, fun h' => wholeP_not_mem_TSP hF (h' ▸ hd)⟩
    simp only [wholeP, Fin.le_def]
    have := d.2.isLt
    omega

omit [NeZero n] in
private theorem arcWidth_lt {d e : Fin n × Fin n} (hde : ArcLe d e) (hne : d ≠ e)
    (hd : d.1 ≤ d.2) : arcWidth d < arcWidth e := by
  obtain ⟨h1, h2⟩ := hde
  have h : d.1.val ≠ e.1.val ∨ d.2.val ≠ e.2.val := by
    by_contra h
    exact hne (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  simp only [arcWidth]
  rw [Fin.le_def] at h1 h2 hd
  omega

end LaminarLite

/-! ## 2. Summing out one coordinate -/

section SumOut

/-- **Summing out one coordinate.**  If `f` does not depend on the coordinate `i`, and `G y b`
does not depend on it either and has `∑_y G y b = r`, then
`|Z| ∑_b f(b) G(b_i, b) = r ∑_b f(b)`.  (Dimension-free.) -/
theorem sum_out {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z] (i : ι)
    (f : (ι → Z) → ℂ) (G : Z → (ι → Z) → ℂ) (r : ℂ)
    (hf : ∀ b x, f (Function.update b i x) = f b)
    (hG : ∀ b x y, G y (Function.update b i x) = G y b)
    (hr : ∀ b, ∑ x, G x b = r) :
    (Fintype.card Z : ℂ) * ∑ b, f b * G (b i) b = r * ∑ b, f b := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | ⟨⟨x0⟩⟩
  · have : IsEmpty (ι → Z) := ⟨fun b => isEmptyElim (b i)⟩
    simp
  set e := Equiv.piSplitAt i (fun _ : ι => Z)
  have hs : ∀ x b', e.symm (x, b') = Function.update (e.symm (x0, b')) i x := by
    intro x b'
    funext j
    by_cases hj : j = i
    · subst hj; simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, hj]
  have hsi : ∀ x b', e.symm (x, b') i = x := by
    intro x b'; rw [hs, Function.update_self]
  have h1 : ∀ x b', f (e.symm (x, b')) = f (e.symm (x0, b')) := by
    intro x b'; rw [hs, hf]
  have h2 : ∀ x y b', G y (e.symm (x, b')) = G y (e.symm (x0, b')) := by
    intro x y b'; rw [hs, hG]
  rw [← Equiv.sum_comp e.symm, ← Equiv.sum_comp e.symm (fun b => f b),
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hl : ∀ x, ∑ b' : {j // j ≠ i} → Z, f (e.symm (x, b')) * G (e.symm (x, b') i) (e.symm (x, b'))
      = ∑ b' : {j // j ≠ i} → Z, f (e.symm (x0, b')) * G x (e.symm (x0, b')) := by
    intro x
    refine sum_congr rfl fun b' _ => ?_
    rw [h1, hsi, h2]
  have hr' : ∀ x, ∑ b' : {j // j ≠ i} → Z, f (e.symm (x, b'))
      = ∑ b' : {j // j ≠ i} → Z, f (e.symm (x0, b')) := fun x => sum_congr rfl fun b' _ => h1 x b'
  simp only [hl, hr']
  rw [sum_comm, sum_const, card_univ, nsmul_eq_mul]
  simp only [← mul_sum, hr]
  rw [← sum_mul]
  ring

end SumOut

/-! ## 3. Fully summed trees -/

section TreeSum

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem card_Z2_cast : (Fintype.card (Z2 L) : ℂ) = (L : ℂ) ^ 2 := by
  simp [Z2, Fintype.card_prod, ZMod.card, sq]

/-- A tree without boundary edges, all labels summed: `∑_b ∏_e E_e(b_e, b_{par e})`. -/
noncomputable def treeZ (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) : ℂ :=
  ∑ b : ↥(nodes F) → Z2 L,
    ∏ d : ↥F, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)

/-- **Peeling.**  If every edge weight has constant column sums `r_e`, then for every set `G`
of edges, `(L²)^{|G|} ∑_b ∏_{e ∈ G} E_e(b_e, b_{par e}) = ∏_{e ∈ G} r_e · ∑_b 1`.  An edge
of `G` of smallest arc is childless in `G`, so its lower label can be summed out
(`sum_out`). -/
theorem treeZ_peel {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) (r : ↥F → ℂ) (hr : ∀ d y, ∑ x, E d x y = r d) :
    ∀ G : Finset ↥F, ((L : ℂ) ^ 2) ^ G.card * ∑ b : ↥(nodes F) → Z2 L,
        ∏ d ∈ G, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩) =
      (∏ d ∈ G, r d) * ∑ _b : ↥(nodes F) → Z2 L, (1 : ℂ) := by
  intro G
  induction G using Finset.strongInduction with
  | H G ih =>
  rcases G.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨e, he, hmin⟩ := G.exists_min_image (fun d : ↥F => arcWidth d.1) hne
  set i : ↥(nodes F) := ⟨e.1, mem_nodes_of_mem e.2⟩
  have hpe := nodePar_up hF e.2
  -- the parents of the other edges of `G` are not `e`
  have hpar : ∀ d ∈ G.erase e, nodePar F d.1 ≠ e.1 := by
    intro d hd heq
    obtain ⟨hdne, hdG⟩ := mem_erase.1 hd
    obtain ⟨hdp, hpd⟩ := nodePar_up hF d.2
    rw [heq] at hdp hpd
    have hdd : d.1.1 ≤ d.1.2 := le_of_lt (isDiag_of_mem_TSP hF d.2).1
    have := arcWidth_lt hdp (Ne.symm hpd) hdd
    exact absurd (hmin d hdG) (not_le.2 this)
  have hself : ∀ d ∈ G.erase e, (⟨d.1, mem_nodes_of_mem d.2⟩ : ↥(nodes F)) ≠ i := by
    intro d hd h
    have h' : d.1 = e.1 := by simpa [i] using congrArg Subtype.val h
    exact (mem_erase.1 hd).1 (Subtype.ext h')
  set f : (↥(nodes F) → Z2 L) → ℂ := fun b =>
    ∏ d ∈ G.erase e, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)
  set Gf : Z2 L → (↥(nodes F) → Z2 L) → ℂ := fun y b =>
    E e y (b ⟨nodePar F e, nodePar_mem F e⟩)
  have hsplit : ∀ b : ↥(nodes F) → Z2 L,
      ∏ d ∈ G, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)
        = f b * Gf (b i) b := by
    intro b
    rw [← mul_prod_erase G _ he, mul_comm]
  have hf : ∀ b x, f (Function.update b i x) = f b := by
    intro b x
    refine prod_congr rfl fun d hd => ?_
    have h1 : (⟨nodePar F d, nodePar_mem F d⟩ : ↥(nodes F)) ≠ i := by
      intro h; exact hpar d hd (congrArg Subtype.val h)
    rw [Function.update_of_ne (hself d hd), Function.update_of_ne h1]
  have hG : ∀ b x y, Gf y (Function.update b i x) = Gf y b := by
    intro b x y
    have h1 : (⟨nodePar F e, nodePar_mem F e⟩ : ↥(nodes F)) ≠ i := by
      intro h; exact hpe.2 (congrArg Subtype.val h)
    simp only [Gf, Function.update_of_ne h1]
  have hsum := sum_out i f Gf (r e) hf hG (fun b => hr e _)
  rw [card_Z2_cast] at hsum
  have hcard : G.card = (G.erase e).card + 1 := (card_erase_add_one he).symm
  have hlt : G.erase e ⊂ G := erase_ssubset he
  have hih := ih _ hlt
  simp only [hsplit]
  rw [hcard, pow_succ, mul_assoc, hsum, ← mul_prod_erase G _ he]
  rw [mul_left_comm, hih]
  ring

/-- **The closed form of a fully summed tree**: `∑_b ∏_e E_e(b_e, b_{par e}) = L² ∏_e r_e`. -/
theorem treeZ_eq {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) (r : ↥F → ℂ) (hr : ∀ d y, ∑ x, E d x y = r d) :
    treeZ F E = (L : ℂ) ^ 2 * ∏ d, r d := by
  have h := treeZ_peel hF E r hr univ
  have hc : Fintype.card ↥(nodes F) = F.card + 1 := by
    rw [Fintype.card_coe, nodes, card_insert_of_notMem (wholeP_not_mem_TSP hF)]
  have hone : ∑ _b : ↥(nodes F) → Z2 L, (1 : ℂ) = ((L : ℂ) ^ 2) ^ (F.card + 1) := by
    rw [sum_const, card_univ, Fintype.card_pi, prod_const, card_univ, hc, nsmul_eq_mul,
      mul_one]
    push_cast
    rw [← card_Z2_cast (L := L)]
  rw [hone, card_univ, Fintype.card_coe] at h
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have hpow : ((L : ℂ) ^ 2) ^ F.card ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hL0)
  unfold treeZ
  apply mul_left_cancel₀ hpow
  rw [h]
  ring

/-- Summing the self-energy over `d` removes the Kronecker deltas. -/
theorem sum_selfW (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) :
    ∑ d : Fin n → Z2 L, selfW L F E d = treeZ F E := by
  unfold selfW treeZ
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_mul]
  have h := (prod_univ_sum (fun _ : Fin n => (univ : Finset (Z2 L)))
    (fun v x => if x = b ⟨leafPar F v, leafPar_mem F v⟩ then (1 : ℂ) else 0)).symm
  rw [Fintype.piFinset_univ] at h
  rw [h]
  simp

end TreeSum

/-! ## 4. The closed forms `Q(σ,π)` and `A(σ,π)` -/

section Closed

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- The column sum of an internal edge `Θ_ξ - 1`, `ξ = t m(s) m(s')`: `(1 - ξ)^{-1} - 1`. -/
noncomputable def edgeR (m : Bool → ℂ) (t : ℝ) (s s' : Bool) : ℂ :=
  (1 - (t : ℂ) * (m s * m s'))⁻¹ - 1

/-- `Q(σ,π) = ∑_{F ∈ T_SP(σ,π)} ∏_{e ∈ F} ((1 - ξ_e)^{-1} - 1)`; it does not depend on `L`. -/
noncomputable def Qlayer (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  ∑ F ∈ TSPlong n σ π, ∏ e ∈ F, edgeR m t (σ e.1) (σ e.2)

/-- `A(σ,π) = L^{-2} ∑_a K^(π)(t,σ,a) = ∏_v (1 - ξ_v)^{-1} · Q(σ,π)` (`sum_Kpi_closed`); it
depends neither on `L` nor on `W`. -/
noncomputable def Alayer (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  (∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) * Qlayer m t σ π

omit [NeZero n] in
/-- Column sums of `Θ_ξ` on `Z_L²`: `∑_x (Θ_ξ)_{xy} = (1 - ξ)^{-1}`. -/
theorem SumZero_sum_Theta_col (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (y : Z2 L) :
    ∑ x : Z2 L, Theta L ξ x y = (1 - ξ)⁻¹ := by
  rw [← sum_Theta_row L hL hξ y]
  refine sum_congr rfl fun x _ => ?_
  exact congrFun (congrFun (Theta_transpose L hL hξ) y) x

omit [NeZero n] in
/-- Column sums of an internal edge weight: `∑_x (Θ_ξ - 1)_{xy} = (1 - ξ)^{-1} - 1`. -/
theorem sum_Theta_sub_one_col (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (y : Z2 L) :
    ∑ x : Z2 L, (Theta L ξ - 1) x y = (1 - ξ)⁻¹ - 1 := by
  simp only [Matrix.sub_apply, sum_sub_distrib, SumZero_sum_Theta_col hL hξ, Matrix.one_apply]
  simp

/-- Re-attaching the leaf edges to the self-energy gives back the tree value (a private copy
of the private `treeValW_eq_sum_selfW` of `Kcal.lean`). -/
private theorem treeValW_eq_sum_selfW' (F : Finset (Fin n × Fin n))
    (a : Fin n → Z2 L) (M : Fin n → Matrix (Z2 L) (Z2 L) ℂ)
    (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) :
    treeValW L F a M E = ∑ d : Fin n → Z2 L, selfW L F E d * ∏ v, M v (a v) (d v) := by
  simp only [selfW, sum_mul]
  rw [sum_comm, treeValW]
  refine sum_congr rfl fun b _ => ?_
  have h : ∀ d : Fin n → Z2 L,
      (∏ v : Fin n, if d v = b ⟨leafPar F v, leafPar_mem F v⟩ then (1 : ℂ) else 0) *
          (∏ e : ↥F, E e (b ⟨e.1, mem_nodes_of_mem e.2⟩) (b ⟨nodePar F e, nodePar_mem F e⟩)) *
        ∏ v, M v (a v) (d v) =
      (∏ e : ↥F, E e (b ⟨e.1, mem_nodes_of_mem e.2⟩) (b ⟨nodePar F e, nodePar_mem F e⟩)) *
        ∏ v, (if d v = b ⟨leafPar F v, leafPar_mem F v⟩ then M v (a v) (d v) else 0) := by
    intro d
    rw [mul_comm (∏ v : Fin n, _), mul_assoc, ← prod_mul_distrib]
    congr 2
    funext v
    split_ifs <;> simp
  simp_rw [h, ← mul_sum]
  rw [mul_comm]
  congr 1
  have := (prod_univ_sum (fun _ : Fin n => (univ : Finset (Z2 L)))
    (fun v x => if x = b ⟨leafPar F v, leafPar_mem F v⟩ then M v (a v) x else 0)).symm
  rw [Fintype.piFinset_univ] at this
  rw [this]
  refine prod_congr rfl fun v _ => ?_
  rw [Fintype.sum_ite_eq']

variable (m : Bool → ℂ) {t : ℝ} (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hm

/-- **(3.47)–(3.48)** on `Z_L²`:
`∑_a K^(π)(t,σ,a) = ∏_i (1 - t m_i m_{i+1})^{-1} ∑_d Σ^(π)(t,σ,d)`. -/
theorem SumZero_sum_Kpi_eq (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ a : Fin n → Z2 L, Kpi L m t σ a π =
      (∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) *
        ∑ d : Fin n → Z2 L, SigmaPi L m t σ π d := by
  have hK : ∀ a : Fin n → Z2 L, Kpi L m t σ a π = ∑ d : Fin n → Z2 L,
      SigmaPi L m t σ π d * ∏ v, thetaEdge L m t (σ v) (σ (v + 1)) (a v) (d v) := by
    intro a
    simp only [Kpi, SigmaPi, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun F _ => ?_
    exact treeValW_eq_sum_selfW' F a _ _
  simp_rw [hK]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [← mul_sum, mul_comm]
  congr 1
  have h := (prod_univ_sum (fun _ : Fin n => (univ : Finset (Z2 L)))
    (fun v x => thetaEdge L m t (σ v) (σ (v + 1)) x (d v))).symm
  rw [Fintype.piFinset_univ] at h
  rw [h]
  refine prod_congr rfl fun v _ => ?_
  exact SumZero_sum_Theta_col hL (hm _ _) (d v)

/-- `∑_d Σ^(π)(t,σ,d) = L² · Q(σ,π)` on `Z_L²`. -/
theorem sum_SigmaPi (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ d : Fin n → Z2 L, SigmaPi L m t σ π d = (L : ℂ) ^ 2 * Qlayer m t σ π := by
  unfold SigmaPi Qlayer
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun F hF => ?_
  have hT : F ∈ TSP n := (mem_filter.1 hF).1
  unfold selfE
  rw [sum_selfW, treeZ_eq hT (fun e => thetaEdge L m t (σ e.1.1) (σ e.1.2) - 1)
    (fun e => edgeR m t (σ e.1.1) (σ e.1.2))
    (fun e y => sum_Theta_sub_one_col hL (hm _ _) y)]
  rw [prod_coe_sort F (fun e => edgeR m t (σ e.1) (σ e.2))]

/-- **The closed form of (3.48)** on `Z_L²`: `∑_a K^(π)(t,σ,a) = L² · A(σ,π)`. -/
theorem sum_Kpi_closed (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ a : Fin n → Z2 L, Kpi L m t σ a π = (L : ℂ) ^ 2 * Alayer m t σ π := by
  rw [SumZero_sum_Kpi_eq m hm hL, sum_SigmaPi m hm hL, Alayer]
  ring

end Closed

/-! ## 5. Translation invariance and the slice form -/

section Slice

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- If every edge weight is translation invariant, so is the self-energy of a tree. -/
private theorem selfW_add_const (F : Finset (Fin n × Fin n))
    (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ)
    (hE : ∀ e x y c, E e (x + c) (y + c) = E e x y) (d : Fin n → Z2 L) (c : Z2 L) :
    selfW L F E (fun v => d v + c) = selfW L F E d := by
  unfold selfW
  rw [← Equiv.sum_comp (Equiv.addRight (fun _ : ↥(nodes F) => c))]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight, Pi.add_apply, add_left_inj, hE]

omit [NeZero n] in
private theorem Theta_sub_one_add_const (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (x y c : Z2 L) : (Theta L ξ - 1) (x + c) (y + c) = (Theta L ξ - 1) x y := by
  simp only [Matrix.sub_apply, Matrix.one_apply, add_left_inj, Theta_apply_add_right L hL hξ]

variable (m : Bool → ℂ) {t : ℝ} (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hm

/-- **Lemma 3.10 (1), translation invariance** on `Z_L²`, for every `σ` and `π`:
`Σ^(π)(t,σ,d + c) = Σ^(π)(t,σ,d)`. -/
theorem SumZero_SigmaPi_add_const (hL : 3 ≤ L) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (d : Fin n → Z2 L) (c : Z2 L) :
    SigmaPi L m t σ π (fun v => d v + c) = SigmaPi L m t σ π d := by
  unfold SigmaPi selfE
  refine sum_congr rfl fun F _ => selfW_add_const F _ (fun e x y c => ?_) d c
  exact Theta_sub_one_add_const hL (hm _ _) x y c

/-- **The slice form**: with the label `d_i = x` fixed,
`∑_{d : d_i = x} Σ^(π)(t,σ,d) = Q(σ,π)`, for every `σ`, `π`, `i` and `x`; the value depends
neither on `L` nor on `x`. -/
theorem SumZero_sum_slice (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
    (i : Fin n) (x : Z2 L) :
    ∑ d ∈ univ.filter (fun d : Fin n → Z2 L => d i = x), SigmaPi L m t σ π d =
      Qlayer m t σ π := by
  set S : Z2 L → ℂ := fun x =>
    ∑ d ∈ univ.filter (fun d : Fin n → Z2 L => d i = x), SigmaPi L m t σ π d with hSdef
  have hS : ∀ x c : Z2 L, S (x + c) = S x := by
    intro x c
    simp only [hSdef, sum_filter]
    rw [← Equiv.sum_comp (Equiv.addRight (fun _ : Fin n => c))]
    refine sum_congr rfl fun d _ => ?_
    simp only [Equiv.coe_addRight, Pi.add_apply, add_left_inj]
    split_ifs
    · exact SumZero_SigmaPi_add_const m hm hL σ π d c
    · rfl
  have hS0 : ∀ x : Z2 L, S x = S 0 := fun x => by
    have := hS 0 x
    rwa [zero_add] at this
  have htot : ∑ d : Fin n → Z2 L, SigmaPi L m t σ π d = (L : ℂ) ^ 2 * S 0 := by
    rw [← sum_fiberwise univ (fun d : Fin n → Z2 L => d i) (SigmaPi L m t σ π)]
    change ∑ y : Z2 L, S y = _
    simp only [hS0, sum_const, card_univ, nsmul_eq_mul]
    rw [card_Z2_cast]
  rw [sum_SigmaPi m hm hL] at htot
  have hL0 : (L : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  have h0 : S 0 = Qlayer m t σ π := (mul_left_cancel₀ hL0 htot).symm
  change S x = _
  rw [hS0, h0]

end Slice

/-! ## 6. Estimates for the Lipschitz step -/

section Estimates

/-- `‖m(s)‖ = 1` in the bulk. -/
private theorem norm_mSig' {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖mSig E s‖ = 1 := by
  cases s <;> simp [mSig, Gauss.norm_spectralM hE]

/-- `‖t m(s) m(s')‖ = t` for `t ≥ 0`. -/
private theorem norm_xi' {E t : ℝ} (hE : |E| ≤ 2) (ht : 0 ≤ t) (s s' : Bool) :
    ‖(t : ℂ) * (mSig E s * mSig E s')‖ = t := by
  rw [norm_mul, norm_mul, norm_mSig' hE, norm_mSig' hE, Complex.norm_real,
    Real.norm_of_nonneg ht, mul_one, mul_one]

private theorem gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < gapK κ := by
  unfold gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

private theorem gapK_le_one (κ : ℝ) : gapK κ ≤ 1 := min_le_left _ _

private theorem gapK_sq_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) :
    gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ gapK κ := (gapK_pos hκ hκ2).le
  have h1 : gapK κ ≤ Real.sqrt (κ * (4 - κ) / 2) := min_le_right _ _
  have h2 : Real.sqrt (κ * (4 - κ) / 2) ^ 2 = κ * (4 - κ) / 2 :=
    Real.sq_sqrt (by nlinarith)
  nlinarith

/-- `|1 - t m²|² = (1 - t)² + t (4 - E²)`. -/
private theorem norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ ^ 2 =
      (1 - t) ^ 2 + t * (4 - E ^ 2) := by
  have hre : (Gauss.spectralM E).re = -E / 2 := by simp [Gauss.spectralM]
  have him := Gauss.spectralM_im E
  have hs := Gauss.spectralM_sqrt_sq hE
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  linear_combination
    ((1 - t * E ^ 2 / 4) * t / 2 + t ^ 2 * (Real.sqrt (4 - E ^ 2) ^ 2 + 4 - E ^ 2) / 16
      + t ^ 2 * E ^ 2 / 4) * hs

/-- **The bulk gap**: `c_κ ≤ |1 - t m(s)²|` for `t ≥ 0` (in particular `t ∈ [0,1]`)
and `|E| ≤ 2 - κ`. -/
private theorem gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t)
    (s : Bool) :
    gapK κ ≤ ‖1 - (t : ℂ) * (mSig E s * mSig E s)‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hsq : gapK κ ^ 2 ≤ ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ ^ 2 := by
    rw [norm_one_sub_sq hE2]
    have hg1 : gapK κ ^ 2 ≤ 1 := by
      have := gapK_le_one κ
      have := (gapK_pos hκ hκ2).le
      nlinarith
    have hg2 := gapK_sq_le hκ hκ2
    by_cases h2 : 2 ≤ 4 - E ^ 2
    · nlinarith
    · nlinarith [sq_nonneg (1 - t - (4 - E ^ 2) / 2)]
  have hle : gapK κ ≤ ‖1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)‖ := by
    have := (gapK_pos hκ hκ2).le
    have := norm_nonneg (1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E))
    nlinarith
  cases s
  · have hc : (1 : ℂ) - (t : ℂ) * (mSig E false * mSig E false) =
        (starRingEnd ℂ) (1 - (t : ℂ) * (Gauss.spectralM E * Gauss.spectralM E)) := by
      simp [mSig, map_sub, map_mul, Complex.conj_ofReal]
    rw [hc, Complex.norm_conj]
    exact hle
  · simpa [mSig] using hle

/-- The factor `f(t) = (1 - tμ)⁻¹ - 1` is bounded by `c⁻¹`. -/
private theorem norm_edge_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : 0 < c) (hct : c ≤ ‖1 - (t : ℂ) * μ‖) :
    ‖(1 - (t : ℂ) * μ)⁻¹ - 1‖ ≤ c⁻¹ := by
  have hne : (1 : ℂ) - (t : ℂ) * μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hct; linarith
  have h : (1 - (t : ℂ) * μ)⁻¹ - 1 = ((t : ℂ) * μ) * (1 - (t : ℂ) * μ)⁻¹ := by
    field_simp
    ring
  rw [h, norm_mul, norm_mul, hμ, Complex.norm_real, Real.norm_of_nonneg ht0, norm_inv, mul_one]
  have hinv : ‖1 - (t : ℂ) * μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hct
  have hc1 : 0 ≤ ‖1 - (t : ℂ) * μ‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  nlinarith [ht1]

/-- The Lipschitz bound `|f(t) - f(1)| ≤ (1 - t) c⁻²`. -/
private theorem norm_edge_sub_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht1 : t ≤ 1)
    (hc : 0 < c) (hct : c ≤ ‖1 - (t : ℂ) * μ‖) (hc1 : c ≤ ‖1 - μ‖) :
    ‖((1 - (t : ℂ) * μ)⁻¹ - 1) - ((1 - μ)⁻¹ - 1)‖ ≤ (1 - t) * c⁻¹ ^ 2 := by
  have hne : (1 : ℂ) - (t : ℂ) * μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hct; linarith
  have hne1 : (1 : ℂ) - μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hc1; linarith
  have h : ((1 - (t : ℂ) * μ)⁻¹ - 1) - ((1 - μ)⁻¹ - 1) =
      (((t - 1 : ℝ) : ℂ) * μ) * ((1 - (t : ℂ) * μ)⁻¹ * (1 - μ)⁻¹) := by
    field_simp
    push_cast
    ring
  rw [h, norm_mul, norm_mul, norm_mul, hμ, Complex.norm_real, norm_inv, norm_inv, mul_one,
    Real.norm_of_nonpos (by linarith), neg_sub]
  have hinv : ‖1 - (t : ℂ) * μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hct
  have hinv1 : ‖1 - μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hc1
  have h01 : 0 ≤ ‖1 - μ‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hprod : ‖1 - (t : ℂ) * μ‖⁻¹ * ‖1 - μ‖⁻¹ ≤ c⁻¹ ^ 2 := by
    rw [sq]; exact mul_le_mul hinv hinv1 h01 (inv_nonneg.2 hc.le)
  exact mul_le_mul_of_nonneg_left hprod (by linarith)

/-- Telescoping bound for finite products:
`‖∏ a - ∏ b‖ ≤ |s| M^{|s|} δ` if `‖a_i‖, ‖b_i‖ ≤ M`, `‖a_i - b_i‖ ≤ δ`, `M ≥ 1`. -/
private theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℂ) {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ M) (hb : ∀ i ∈ s, ‖b i‖ ≤ M) (hab : ∀ i ∈ s, ‖a i - b i‖ ≤ δ) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ s.card * M ^ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ M := fun i hi => ha i (mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ M := fun i hi => hb i (mem_insert_of_mem hi)
    have hab' : ∀ i ∈ s, ‖a i - b i‖ ≤ δ := fun i hi => hab i (mem_insert_of_mem hi)
    have hI := ih ha' hb' hab'
    have hax := ha x (mem_insert_self x s)
    have habx := hab x (mem_insert_self x s)
    have hQ : ‖∏ i ∈ s, b i‖ ≤ M ^ s.card := by
      rw [norm_prod]
      calc ∏ i ∈ s, ‖b i‖ ≤ ∏ _i ∈ s, M :=
            prod_le_prod₀ (fun i _ => norm_nonneg _) hb'
        _ = M ^ s.card := prod_const M
    rw [prod_insert hx, prod_insert hx, card_insert_of_notMem hx]
    have hsplit : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i =
        a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by ring
    rw [hsplit]
    have hMk : M ^ s.card ≤ M ^ s.card * M := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hM (Nat.le_succ _)
    have hM0 : 0 ≤ M := by linarith
    have hMk0 : 0 ≤ M ^ s.card := pow_nonneg hM0 _
    have hk0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    calc ‖a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i‖
        ≤ ‖a x‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ + ‖a x - b x‖ * ‖∏ i ∈ s, b i‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ M * (s.card * M ^ s.card * δ) + δ * M ^ s.card := by
          gcongr
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * M ^ (s.card + 1) * δ := by
          push_cast
          rw [pow_succ]
          nlinarith [mul_le_mul_of_nonneg_left hMk hδ]

/-- A vertex `v` strictly inside the arc of `d` and not strictly inside the arc of any other
diagonal of `F` below `d`. -/
private def goodPt {n : ℕ} (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n) (v : Fin n) :
    Prop :=
  d.1 < v ∧ v < d.2 ∧ ∀ e ∈ F, e ≠ d → ArcLe e d → ¬(e.1 < v ∧ v < e.2)

private theorem exists_goodPt {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d : Fin n × Fin n} (hd : d ∈ F) : ∃ v, goodPt F d v := by
  have hdD := isDiag_of_mem_TSP hF hd
  have hcf := crossingFree_of_mem_TSP hF
  obtain ⟨hd12, hdadj, -⟩ := hdD
  rw [Fin.lt_def] at hd12
  set S := F.filter (fun e => e.1 = d.1 ∧ e.2 < d.2) with hSdef
  rcases S.eq_empty_or_nonempty with hS | hS
  · have hlt : d.1.val + 1 < n := by have := d.2.isLt; omega
    refine ⟨⟨d.1.val + 1, hlt⟩, ?_, ?_, ?_⟩
    · rw [Fin.lt_def]; simp
    · rw [Fin.lt_def]; simp only; omega
    · rintro e he hne ⟨hle1, hle2⟩ ⟨h1, h2⟩
      rw [Fin.lt_def] at h1 h2
      rw [Fin.le_def] at hle1 hle2
      simp only at h1 h2
      have he1 : e.1 = d.1 := Fin.ext (by omega)
      have he2 : e.2 < d.2 := by
        rw [Fin.lt_def]
        rcases Nat.lt_or_ge e.2.val d.2.val with h | h
        · exact h
        · exact absurd (Prod.ext he1 (Fin.ext (by omega))) hne
      have : e ∈ S := mem_filter.2 ⟨he, he1, he2⟩
      rw [hS] at this
      exact absurd this (notMem_empty e)
  · obtain ⟨e₀, he₀, hmax⟩ := S.exists_max_image (fun e => e.2.val) hS
    obtain ⟨he₀F, he₀1, he₀2⟩ := mem_filter.1 he₀
    have he₀D := (isDiag_of_mem_TSP hF he₀F).1
    rw [Fin.lt_def] at he₀D he₀2
    have he₀1' : e₀.1.val = d.1.val := congrArg Fin.val he₀1
    refine ⟨e₀.2, ?_, ?_, ?_⟩
    · rw [Fin.lt_def]; omega
    · rw [Fin.lt_def]; omega
    · rintro e he hne ⟨hle1, hle2⟩ ⟨h1, h2⟩
      rw [Fin.lt_def] at h1 h2
      rw [Fin.le_def] at hle1 hle2
      rcases Nat.lt_or_ge d.1.val e.1.val with h | h
      · apply hcf e₀ he₀F e he
        left
        refine ⟨?_, ?_, ?_⟩ <;> rw [Fin.lt_def] <;> omega
      · have he1 : e.1 = d.1 := Fin.ext (by omega)
        have he2 : e.2 < d.2 := by
          rw [Fin.lt_def]
          rcases Nat.lt_or_ge e.2.val d.2.val with h' | h'
          · exact h'
          · exact absurd (Prod.ext he1 (Fin.ext (by omega))) hne
        have : e.2.val ≤ e₀.2.val := hmax e (mem_filter.2 ⟨he, he1, he2⟩)
        omega

private theorem goodPt_inj {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d d' : Fin n × Fin n} (hd : d ∈ F) (hd' : d' ∈ F) {v : Fin n}
    (hv : goodPt F d v) (hv' : goodPt F d' v) : d = d' := by
  by_contra hne
  have hcf := crossingFree_of_mem_TSP hF
  obtain ⟨a1, a2, a3⟩ := hv
  obtain ⟨b1, b2, b3⟩ := hv'
  by_cases h1 : ArcLe d' d
  · exact a3 d' hd' (Ne.symm hne) h1 ⟨b1, b2⟩
  by_cases h2 : ArcLe d d'
  · exact b3 d hd hne h2 ⟨a1, a2⟩
  simp only [ArcLe, Fin.le_def, not_and_or, not_le] at h1 h2
  rw [Fin.lt_def] at a1 a2 b1 b2
  have hc1 := hcf d hd d' hd'
  have hc2 := hcf d' hd' d hd
  simp only [Crossing, Fin.lt_def, not_or, not_and_or, not_lt] at hc1 hc2
  omega

/-- A crossing-free set of diagonals of the `n`-gon has at most `n - 2` elements. -/
private theorem card_le_of_mem_TSP {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) :
    F.card ≤ n - 2 := by
  classical
  let g : Fin n × Fin n → Fin n := fun d =>
    if h : ∃ v, goodPt F d v then Classical.choose h else d.1
  have hg : ∀ d ∈ F, goodPt F d (g d) := by
    intro d hd
    have h := exists_goodPt hF hd
    simp only [g, h, ↓reduceDIte]
    exact Classical.choose_spec h
  have hcard : (Finset.Ioo 0 (n - 1)).card = n - 2 := by
    rw [Nat.card_Ioo]; omega
  rw [← hcard]
  refine card_le_card_of_injOn (fun d => (g d).val) (fun d hd => ?_) (fun d hd d' hd' h => ?_)
  · obtain ⟨h1, h2, -⟩ := hg d hd
    rw [Fin.lt_def] at h1 h2
    have := d.2.isLt
    simp only [coe_Ioo, Set.mem_Ioo]
    omega
  · have hv : g d = g d' := Fin.ext h
    have g' := hg d' hd'
    rw [← hv] at g'
    exact goodPt_inj hF hd hd' (hg d hd) g'

/-- The number of trees: `#T_SP(σ,π) ≤ #T_SP(n) ≤ 2^{n²}`. -/
private theorem card_TSPlong_le (n : ℕ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    (TSPlong n σ π).card ≤ 2 ^ (n ^ 2) := by
  calc (TSPlong n σ π).card ≤ (TSP n).card := card_filter_le _ _
    _ ≤ (diagonals n).powerset.card := card_filter_le _ _
    _ = 2 ^ (diagonals n).card := card_powerset _
    _ ≤ 2 ^ (n ^ 2) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        calc (diagonals n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_le_univ _
          _ = n ^ 2 := by simp [sq]

end Estimates

/-! ## 7. The slice form for `σ^{(alt)}` and the sum-zero bound given `Q(1) = 0` -/

section SumZero

/-- **The slice form** under the hypotheses of `SigmaPi_alt_sumZero_le_of_Qlayer_one`:
`∑_{d : d₀ = d₁} Σ^{(∅)}(t, σ^{(alt)}, d) = Q(σ^{(alt)}, ∅)`, independent of `L` and `d₁`. -/
theorem SumZero_sum_slice_alt :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → ∀ d₁ : Z2 L,
      ∑ d ∈ Finset.univ.filter (fun d : Fin n → Z2 L => d ⟨0, by omega⟩ = d₁),
          SigmaPi L (mSig E) t (sigAlt n) ∅ d = Qlayer (mSig E) t (sigAlt n) ∅ := by
  intro κ hκ L _ hL E hE t ht n _ hn _ d₁
  have hE2 : |E| ≤ 2 := by linarith
  have hm : ∀ s s' : Bool, ‖(t : ℂ) * (mSig E s * mSig E s')‖ < 1 := fun s s' => by
    rw [norm_xi' hE2 ht.1]; exact ht.2
  exact SumZero_sum_slice (mSig E) hm hL (sigAlt n) ∅ ⟨0, by omega⟩ d₁

/-- The `L`-free Lipschitz bound: `‖Q(σ^{(alt)}, ∅)(t)‖ ≤ 2^{n²} n c_κ^{-n} (1 - t)` when
`Q(σ^{(alt)}, ∅)(1) = 0`. -/
private theorem norm_Qlayer_le {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (hn : 2 ≤ n) (σ : Fin n → Bool)
    (hQ1 : Qlayer (mSig E) 1 σ ∅ = 0) :
    ‖Qlayer (mSig E) t σ ∅‖ ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (1 - t) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hc := gapK_pos hκ hκ2
  set c := gapK κ with hcdef
  have hc1 : 1 ≤ c⁻¹ := one_le_inv₀ hc |>.2 (gapK_le_one κ)
  have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hμ : ∀ s : Bool, ‖mSig E s * mSig E s‖ = 1 := fun s => by
    rw [norm_mul, norm_mSig' hE2]; norm_num
  -- one tree
  have hF : ∀ F ∈ TSPlong n σ ∅,
      ‖∏ e ∈ F, edgeR (mSig E) t (σ e.1) (σ e.2) - ∏ e ∈ F, edgeR (mSig E) 1 (σ e.1) (σ e.2)‖
        ≤ n * c⁻¹ ^ n * (1 - t) := by
    intro F hFm
    obtain ⟨hFT, hFl⟩ := mem_filter.1 hFm
    have hsame : ∀ e ∈ F, σ e.2 = σ e.1 := by
      intro e he
      by_contra h
      have : e ∈ Flong F σ := mem_filter.2 ⟨he, Ne.symm h⟩
      rw [hFl] at this
      exact notMem_empty e this
    have hk := card_le_of_mem_TSP hFT
    have htel := norm_prod_sub_prod_le F (fun e => edgeR (mSig E) t (σ e.1) (σ e.2))
      (fun e => edgeR (mSig E) 1 (σ e.1) (σ e.2)) hc1 (by positivity : 0 ≤ (1 - t) * c⁻¹ ^ 2)
      (fun e he => by
        simp only [edgeR, hsame e he]
        exact norm_edge_le (hμ _) ht.1 ht.2.le hc (gapK_le_norm hκ hE ht.1 _))
      (fun e he => by
        simp only [edgeR, hsame e he]
        exact norm_edge_le (hμ _) zero_le_one le_rfl hc (gapK_le_norm hκ hE zero_le_one _))
      (fun e he => by
        simp only [edgeR, hsame e he]
        have h1 := gapK_le_norm hκ hE zero_le_one (σ e.1)
        rw [Complex.ofReal_one, one_mul] at h1 ⊢
        exact norm_edge_sub_le (hμ _) ht.2.le hc (gapK_le_norm hκ hE ht.1 _) h1)
    refine htel.trans ?_
    have hkn : (F.card : ℝ) ≤ n := by
      have : F.card ≤ n := by omega
      exact_mod_cast this
    have hpow : c⁻¹ ^ F.card * c⁻¹ ^ 2 ≤ c⁻¹ ^ n := by
      rw [← pow_add]; exact pow_le_pow_right₀ hc1 (by omega)
    have hp0 : 0 ≤ c⁻¹ ^ F.card * c⁻¹ ^ 2 := by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    calc (F.card : ℝ) * c⁻¹ ^ F.card * ((1 - t) * c⁻¹ ^ 2)
        = (F.card : ℝ) * (c⁻¹ ^ F.card * c⁻¹ ^ 2) * (1 - t) := by ring
      _ ≤ n * c⁻¹ ^ n * (1 - t) := by gcongr
  have hdiff : Qlayer (mSig E) t σ ∅ = ∑ F ∈ TSPlong n σ ∅,
      (∏ e ∈ F, edgeR (mSig E) t (σ e.1) (σ e.2) - ∏ e ∈ F, edgeR (mSig E) 1 (σ e.1) (σ e.2)) := by
    rw [sum_sub_distrib]
    have : Qlayer (mSig E) 1 σ ∅ = ∑ F ∈ TSPlong n σ ∅,
        ∏ e ∈ F, edgeR (mSig E) 1 (σ e.1) (σ e.2) := rfl
    rw [← this, hQ1, sub_zero]
    rfl
  rw [hdiff]
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_sum hF).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard : ((TSPlong n σ ∅).card : ℝ) ≤ 2 ^ (n ^ 2) := by
    exact_mod_cast card_TSPlong_le n σ ∅
  have h0 : 0 ≤ (n : ℝ) * c⁻¹ ^ n * (1 - t) := by positivity
  calc ((TSPlong n σ ∅).card : ℝ) * (n * c⁻¹ ^ n * (1 - t))
      ≤ 2 ^ (n ^ 2) * (n * c⁻¹ ^ n * (1 - t)) := mul_le_mul_of_nonneg_right hcard h0
    _ = 2 ^ (n ^ 2) * n * c⁻¹ ^ n * (1 - t) := by ring

/-- `1 - t = η_t / Im m ≤ (2 / √(κ(4-κ))) η_t` in the bulk `|E| ≤ 2 - κ`. -/
private theorem one_sub_le_etaT {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht1 : t ≤ 1) :
    1 - t ≤ (2 / Real.sqrt (κ * (4 - κ))) * etaT E t := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hq0 : 0 < κ * (4 - κ) := by nlinarith
  have hsq0 : 0 < Real.sqrt (κ * (4 - κ)) := Real.sqrt_pos.2 hq0
  have hsq : Real.sqrt (κ * (4 - κ)) ≤ Real.sqrt (4 - E ^ 2) := Real.sqrt_le_sqrt hq
  rw [etaT, Gauss.spectralZ_im, Gauss.spectralM_im]
  have h : 2 / Real.sqrt (κ * (4 - κ)) * ((1 - t) * (Real.sqrt (4 - E ^ 2) / 2)) =
      (1 - t) * (Real.sqrt (4 - E ^ 2) / Real.sqrt (κ * (4 - κ))) := by
    field_simp
  rw [h]
  have h1 : 1 ≤ Real.sqrt (4 - E ^ 2) / Real.sqrt (κ * (4 - κ)) := (one_le_div hsq0).2 hsq
  nlinarith

/-- **The sum-zero bound given `Q(1) = 0`** (the bound `SigmaPi_alt_sumZero_le` under the extra
hypothesis `Qlayer (mSig E) 1 (sigAlt n) ∅ = 0`, after `Even n`). -/
theorem SigmaPi_alt_sumZero_le_of_Qlayer_one :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n →
      Qlayer (mSig E) 1 (sigAlt n) ∅ = 0 → ∀ d₁ : Z2 L,
      ‖∑ d ∈ Finset.univ.filter (fun d : Fin n → Z2 L => d ⟨0, by omega⟩ = d₁),
          SigmaPi L (mSig E) t (sigAlt n) ∅ d‖
        ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) * etaT E t := by
  intro κ hκ L _ hL E hE t ht n _ hn hev hQ1 d₁
  rw [SumZero_sum_slice_alt κ hκ L hL E hE t ht n hn hev d₁]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hQ := norm_Qlayer_le hκ hE ht (by omega) (sigAlt n) hQ1
  have hη := one_sub_le_etaT hκ hE ht.2.le
  have hc := gapK_pos hκ hκ2
  have hA : 0 ≤ (2 : ℝ) ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n := by positivity
  calc ‖Qlayer (mSig E) t (sigAlt n) ∅‖
      ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (1 - t) := hQ
    _ ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * ((2 / Real.sqrt (κ * (4 - κ))) * etaT E t) :=
        mul_le_mul_of_nonneg_left hη hA
    _ = 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) * etaT E t := by
        ring

end SumZero

end RBM.KLoop
