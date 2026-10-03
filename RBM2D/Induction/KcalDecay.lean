/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Loop.Kcal
import RBM2D.Propagator.Prop5

/-!
# Fast decay of the primitive loop `𝒦` at far labels (`kcalDecay`)

Result (namespace `RBM.Ind`): the statement `KcalDecay` (`RBM2D.Induction.HierVocab`) with no
added hypothesis:

* `kcalDecay (κ : ℝ) : KcalDecay κ`.

Source: `eq:bcal_k` and the tree representation of `𝒦` (`RBM2D.Loop.Kcal`, [50] (3.5) in
`d = 2`); used by `lem_decayLoop` and `lem_BcalE`.

Proof (deterministic):
1. `k = 1`: `maxDist a = 0`, so the premise `ℓ_u W^τ ≤ maxDist a` fails.
2. `k ≥ 2`: `maxDist a ≤ L` (`zdist2_le_L`), so for `W ≥ 2` the premise forces `ℓ_u < L`, i.e.
   `ℓ_u = (1-u)^{-1/2}`.
3. Every edge parameter of the tree representation is `ξ = u m(s) m(s')` with `|m| = 1`, so
   `‖ξ‖ = u` and `|1-ξ| ≥ 1-u`; hence `ℓ̂(ξ) = κ_ξ⁻¹ ≤ ℓ_u` and the prefactor
   `(κ_ξ² ℓ̂(ξ)²)⁻¹` of property 5 (`norm_Theta_apply_le_prop5`) is `1`.  The leaf kernels `Θ_ξ`
   and the internal kernels `Θ_ξ - 1` are `≤ B e^{-κ' |x-y|_L}`, `κ' = 1/(20000 ℓ_u)`,
   `B = 180·40002²(1 + log L) + 1`.  The bulk gap `gapK` is not needed, and `|E| ≤ 2 - κ` is used
   only as `|E| ≤ 2` (`|m| = 1`).
4. `k = 2`: one edge (`Kcal_two`).  `k ≥ 3`: `Kcal_eq_sum_Kpi` gives `∑_{F ∈ TSP k} Γ_F`; each
   `Γ_F` is a sum over `(L²)^{|nodes F|}` internal labels of terms `≤ B^{k+|F|} e^{-κ' D}`, `D` the
   total edge length, and `dist_bounds` gives `maxDist a ≤ D` (any two vertices of the tree are at
   distance at most its total edge length).  The crude counts `|TSP k| ≤ 2^{k²}`, `|F|, |nodes F| ≤
   k²` suffice: only a power `N^Q`, `Q` depending on `k`, is lost.
5. `A N^Q e^{-W^τ/20000} ≤ W^{-D}` eventually in `N`, from `W^τ ≥ N^{𝔠τ}`, `W ≤ N` and
   `x^s e^{-b x} → 0` (`kcalDecay_eventually`).

Sections 1-3 (all `private`) repeat the tree-representation lemmas of `RBM2D.Loop.PureLoop` (the
laminar structure of crossing-free sets, `nodes_laminar`, `nodePar_spec`); the path bound
`dist_bounds` (leaf-to-leaf distance at most the total edge length) is specific to this setting.
Sections 4-8 and the theorem are specific to this file.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.KLoop

open Finset

/-! ## 1. Distances on `Z_L²` -/

section Dist

variable {L : ℕ} [NeZero L]

private theorem zdist_neg' (u : ZMod L) : zdist L (-u) = zdist L u := by
  by_cases h : u = 0
  · simp [h]
  · have hu : u.val < L := ZMod.val_lt u
    have hne : u.val ≠ 0 := by
      intro h0; exact h ((ZMod.val_eq_zero u).1 h0)
    simp only [zdist, ZMod.neg_val, h, ite_false]
    omega

private theorem zdist2_neg' (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, zdist_neg']

private theorem zdist2_symm (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
  rw [← zdist2_neg', neg_sub]

private theorem zdist2_tri (x y z : Z2 L) :
    zdist2 L (x - z) ≤ zdist2 L (x - y) + zdist2 L (y - z) := by
  have := zdist2_add_le L (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this

end Dist

/-! ## 2. The laminar structure of a crossing-free set

The statements (`IsTSP`, `nodes_laminar`, `nodePar_spec`, and the arc lemmas) are
dimension-free. -/

section Laminar

variable {n : ℕ}

private def IsTSPf (F : Finset (Fin n × Fin n)) : Prop :=
  (∀ d ∈ F, IsDiag n d.1 d.2) ∧ CrossingFree F

private theorem isTSPf_of_mem {F : Finset (Fin n × Fin n)} (h : F ∈ TSP n) : IsTSPf F := by
  simp only [TSP, mem_filter, mem_powerset] at h
  refine ⟨fun d hd => ?_, h.2⟩
  have := h.1 hd
  simpa [diagonals] using this

variable [NeZero n]

private theorem minNode_le {s : Finset (Fin n × Fin n)} {e : Fin n × Fin n} (he : e ∈ s) :
    minNode s ∈ s ∧ arcWidth (minNode s) ≤ arcWidth e := by
  have h : s.Nonempty := ⟨e, he⟩
  unfold minNode
  split_ifs
  exact ⟨(Classical.choose_spec (s.exists_min_image arcWidth h)).1,
    (Classical.choose_spec (s.exists_min_image arcWidth h)).2 e he⟩

private theorem arcLe_wholeP (d : Fin n × Fin n) : ArcLe d (wholeP n) := by
  refine ⟨Fin.zero_le _, ?_⟩
  simp only [wholeP, Fin.le_def]
  have := d.2.isLt
  omega

private theorem lt_of_mem_nodes {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) (hn : 2 ≤ n)
    {d : Fin n × Fin n} (hd : d ∈ nodes F) : d.1 < d.2 := by
  rcases mem_insert.1 hd with rfl | hd
  · simp only [wholeP, Fin.lt_def, Fin.val_zero]; omega
  · exact (hF.1 d hd).1

private theorem nodes_laminar {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) {d e : Fin n × Fin n}
    (hd : d ∈ nodes F) (he : e ∈ nodes F) :
    ArcLe d e ∨ ArcLe e d ∨ d.2 ≤ e.1 ∨ e.2 ≤ d.1 := by
  rcases mem_insert.1 he with rfl | he'
  · exact Or.inl (arcLe_wholeP d)
  rcases mem_insert.1 hd with rfl | hd'
  · exact Or.inr (Or.inl (arcLe_wholeP e))
  have h1 := hF.2 d hd' e he'
  have hd2 := (hF.1 d hd').1
  have he2 := (hF.1 e he').1
  simp only [Crossing, not_or, not_and, not_lt] at h1
  simp only [ArcLe, Fin.le_def, Fin.lt_def] at h1 hd2 he2 ⊢
  omega

omit [NeZero n] in
private theorem arcLe_trans {d e f : Fin n × Fin n} (h1 : ArcLe d e) (h2 : ArcLe e f) :
    ArcLe d f := by
  simp only [ArcLe, Fin.le_def] at *
  omega

omit [NeZero n] in
private theorem arcLe_antisymm {d e : Fin n × Fin n} (h1 : ArcLe d e) (h2 : ArcLe e d) :
    d = e := by
  simp only [ArcLe, Fin.le_def] at *
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

omit [NeZero n] in
private theorem eq_of_arcLe_of_width {d e : Fin n × Fin n} (hd : d.1 ≤ d.2) (h : ArcLe d e)
    (hw : arcWidth e ≤ arcWidth d) : d = e := by
  simp only [ArcLe, arcWidth, Fin.le_def] at *
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

private theorem arcLe_total_of_arcLe {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) (hn : 2 ≤ n)
    {d e e' : Fin n × Fin n} (hd : d ∈ nodes F) (he : e ∈ nodes F) (he' : e' ∈ nodes F)
    (h1 : ArcLe d e) (h2 : ArcLe d e') : ArcLe e e' ∨ ArcLe e' e := by
  have hlt := lt_of_mem_nodes hF hn hd
  rcases nodes_laminar hF he he' with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp only [ArcLe, Fin.le_def, Fin.lt_def] at h1 h2 h hlt; omega
  · simp only [ArcLe, Fin.le_def, Fin.lt_def] at h1 h2 h hlt; omega

/-- `nodePar` is the smallest strict container of a node other than `whole`. -/
private theorem nodePar_spec {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) (hn : 2 ≤ n)
    {d : Fin n × Fin n} (hd : d ∈ nodes F) (hdw : d ≠ wholeP n) :
    nodePar F d ∈ nodes F ∧ ArcLe d (nodePar F d) ∧ nodePar F d ≠ d ∧
      ∀ e ∈ nodes F, ArcLe d e → e ≠ d → ArcLe (nodePar F d) e := by
  have hW : wholeP n ∈ (nodes F).filter fun e => ArcLe d e ∧ e ≠ d :=
    mem_filter.2 ⟨wholeP_mem_nodes F, arcLe_wholeP d, fun h => hdw h.symm⟩
  obtain ⟨h1, h2⟩ := minNode_le hW
  have hm := mem_filter.1 h1
  have hlt := lt_of_mem_nodes hF hn hd
  refine ⟨hm.1, hm.2.1, hm.2.2, fun e he hde hne => ?_⟩
  rcases arcLe_total_of_arcLe hF hn hd hm.1 he hm.2.1 hde with h | h
  · exact h
  · have hemem : e ∈ (nodes F).filter fun e => ArcLe d e ∧ e ≠ d := mem_filter.2 ⟨he, hde, hne⟩
    have := (minNode_le hemem).2
    have he12 : e.1 ≤ e.2 := le_trans hde.1 (le_trans (le_of_lt hlt) hde.2)
    rw [eq_of_arcLe_of_width he12 h this]
    exact ⟨le_refl _, le_refl _⟩

end Laminar

/-! ## 3. The path bound: the distance between two vertices of a tree is at most its total
edge length.

This is sharper than routing every pair of leaves through the root, which only gives `2 ×` the
total length. -/

section Path

variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]

/-- The edge length above the node `e`. -/
private noncomputable def elen (F : Finset (Fin n × Fin n)) (β : Fin n × Fin n → Z2 L)
    (e : Fin n × Fin n) : ℕ :=
  zdist2 L (β e - β (nodePar F e))

/-- The edges on the path between the nodes `x` and `y`: those above exactly one of them. -/
private def pathSet (F : Finset (Fin n × Fin n)) (x y : Fin n × Fin n) :
    Finset (Fin n × Fin n) :=
  F.filter fun e => ¬(ArcLe x e ↔ ArcLe y e)

private theorem anc_step {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) (hn : 2 ≤ n)
    {x : Fin n × Fin n} (hx : x ∈ nodes F) (hxw : x ≠ wholeP n) :
    nodePar F x ∈ nodes F ∧ ArcLe x (nodePar F x) ∧ ¬ArcLe (nodePar F x) x ∧ x ∈ F ∧
      (F.filter (ArcLe (nodePar F x))).card < (F.filter (ArcLe x)).card ∧
      ∀ e ∈ F, e ≠ x → (ArcLe x e ↔ ArcLe (nodePar F x) e) := by
  have hxF : x ∈ F := (mem_insert.1 hx).resolve_left hxw
  obtain ⟨hp, hdp, hne, hmin⟩ := nodePar_spec hF hn hx hxw
  have hpd : ¬ArcLe (nodePar F x) x := fun h => hne (arcLe_antisymm hdp h).symm
  have hsub : F.filter (ArcLe (nodePar F x)) ⊆ (F.filter (ArcLe x)).erase x := by
    intro e he
    obtain ⟨heF, hpe⟩ := mem_filter.1 he
    refine mem_erase.2 ⟨?_, mem_filter.2 ⟨heF, arcLe_trans hdp hpe⟩⟩
    rintro rfl
    exact hpd hpe
  have hxmem : x ∈ F.filter (ArcLe x) := mem_filter.2 ⟨hxF, le_rfl, le_rfl⟩
  have hcard : (F.filter (ArcLe (nodePar F x))).card < (F.filter (ArcLe x)).card := by
    have h1 := card_le_card hsub
    rw [card_erase_of_mem hxmem] at h1
    have := card_pos.2 ⟨x, hxmem⟩
    omega
  exact ⟨hp, hdp, hpd, hxF, hcard, fun e he hex =>
    ⟨fun h => hmin e (mem_nodes_of_mem he) h hex, fun h => arcLe_trans hdp h⟩⟩

private theorem path_aux {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) (hn : 2 ≤ n)
    (β : Fin n × Fin n → Z2 L) :
    ∀ k : ℕ, ∀ x ∈ nodes F, ∀ y ∈ nodes F,
      (F.filter (ArcLe x)).card + (F.filter (ArcLe y)).card = k →
      zdist2 L (β x - β y) ≤ ∑ e ∈ pathSet F x y, elen F β e := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have key : ∀ x ∈ nodes F, ∀ y ∈ nodes F,
        (F.filter (ArcLe x)).card + (F.filter (ArcLe y)).card = k → x ≠ wholeP n →
          ¬ArcLe y x → zdist2 L (β x - β y) ≤ ∑ e ∈ pathSet F x y, elen F β e := by
      intro x hx y hy hk hxw hyx
      obtain ⟨hp, hdp, hpd, hxF, hcard, hiff⟩ := anc_step hF hn hx hxw
      have hih := ih _ (by omega) (nodePar F x) hp y hy rfl
      have htri := zdist2_tri (β x) (β (nodePar F x)) (β y)
      have hxn : x ∉ pathSet F (nodePar F x) y := by
        intro h
        exact (mem_filter.1 h).2 ⟨fun h' => absurd h' hpd, fun h' => absurd h' hyx⟩
      have hsub : insert x (pathSet F (nodePar F x) y) ⊆ pathSet F x y := by
        intro e he
        rcases mem_insert.1 he with rfl | he
        · exact mem_filter.2 ⟨hxF, fun h => hyx (h.1 ⟨le_rfl, le_rfl⟩)⟩
        · obtain ⟨heF, hne⟩ := mem_filter.1 he
          have hex : e ≠ x := by
            rintro rfl; exact hxn he
          exact mem_filter.2 ⟨heF, fun h => hne ((hiff e heF hex).symm.trans h)⟩
      have hs := sum_le_sum_of_subset (f := elen F β) hsub
      rw [sum_insert hxn] at hs
      have : elen F β x = zdist2 L (β x - β (nodePar F x)) := rfl
      omega
    intro x hx y hy hk
    by_cases h1 : x ≠ wholeP n ∧ ¬ArcLe y x
    · exact key x hx y hy hk h1.1 h1.2
    by_cases h2 : y ≠ wholeP n ∧ ¬ArcLe x y
    · have := key y hy x hx (by omega) h2.1 h2.2
      have hs : pathSet F y x = pathSet F x y := by
        ext e; simp only [pathSet, mem_filter, iff_comm]
      rw [hs] at this
      rwa [zdist2_symm]
    · have hyx : ArcLe y x := by
        by_contra hc
        exact h1 ⟨fun hxw => hc (hxw ▸ arcLe_wholeP y), hc⟩
      have hxy : ArcLe x y := by
        by_contra hc
        exact h2 ⟨fun hyw => hc (hyw ▸ arcLe_wholeP x), hc⟩
      have := arcLe_antisymm hxy hyx
      subst this
      simp

/-- Any two nodes of the tree are at distance at most the total length of the internal edges. -/
private theorem path_le {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) (hn : 2 ≤ n)
    (β : Fin n × Fin n → Z2 L) {x y : Fin n × Fin n} (hx : x ∈ nodes F) (hy : y ∈ nodes F) :
    zdist2 L (β x - β y) ≤ ∑ e ∈ F, zdist2 L (β e - β (nodePar F e)) :=
  (path_aux hF hn β _ x hx y hy rfl).trans (sum_le_sum_of_subset (filter_subset _ _))

/-- **Pointwise part of the tree bound.**  With `D` the total edge length of the labelling `β`
(leaf edges plus internal edges), any two leaves are at distance at most `D`, and every node is
within `D` of any given leaf. -/
private theorem dist_bounds {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) (hn : 2 ≤ n)
    (a : Fin n → Z2 L) (β : Fin n × Fin n → Z2 L) (i : Fin n) :
    (∀ j, zdist2 L (a i - a j) ≤
      (∑ v, zdist2 L (a v - β (leafPar F v)) + ∑ e ∈ F, zdist2 L (β e - β (nodePar F e)))) ∧
    (∀ d ∈ nodes F, zdist2 L (a i - β d) ≤
      (∑ v, zdist2 L (a v - β (leafPar F v)) + ∑ e ∈ F, zdist2 L (β e - β (nodePar F e)))) := by
  set Ls := ∑ v, zdist2 L (a v - β (leafPar F v))
  set Es := ∑ e ∈ F, zdist2 L (β e - β (nodePar F e))
  have hleaf : ∀ v, zdist2 L (a v - β (leafPar F v)) ≤ Ls := fun v =>
    single_le_sum (f := fun v => zdist2 L (a v - β (leafPar F v))) (fun _ _ => Nat.zero_le _)
      (mem_univ v)
  refine ⟨fun j => ?_, fun d hd => ?_⟩
  · by_cases hij : i = j
    · subst hij; simp
    · have hpair : zdist2 L (a i - β (leafPar F i)) + zdist2 L (a j - β (leafPar F j)) ≤ Ls := by
        have := sum_le_sum_of_subset (f := fun v => zdist2 L (a v - β (leafPar F v)))
          (show ({i, j} : Finset (Fin n)) ⊆ univ from subset_univ _)
        rwa [sum_pair hij] at this
      have h1 := zdist2_tri (a i) (β (leafPar F i)) (a j)
      have h2 := zdist2_tri (β (leafPar F i)) (β (leafPar F j)) (a j)
      have h3 := path_le hF hn β (leafPar_mem F i) (leafPar_mem F j)
      have h4 : zdist2 L (β (leafPar F j) - a j) = zdist2 L (a j - β (leafPar F j)) :=
        zdist2_symm _ _
      omega
  · have h1 := zdist2_tri (a i) (β (leafPar F i)) (β d)
    have h2 := path_le hF hn β (leafPar_mem F i) hd
    have h3 := hleaf i
    omega

end Path

/-! ## 4. A tree with exponentially decaying edges decays

Crude count of the internal labels: there are `(L²)^{|nodes F|}` of them, and the summand is
bounded by `B^{n + |F|} e^{-κ D}`, `D` the total edge length, which dominates `maxDist a`
(`dist_bounds`).  The polynomial loss `(L²)^{n²}` is harmless: it is absorbed by `e^{-W^τ/20000}`
at the end. -/

section TreeBound

variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]

private theorem kcalDecay_tree_bound {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) (hn : 2 ≤ n)
    (a : Fin n → Z2 L) (M : Fin n → Matrix (Z2 L) (Z2 L) ℂ)
    (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) {B κ : ℝ} (hB : 1 ≤ B) (hκ : 0 ≤ κ)
    (hM : ∀ v x y, ‖M v x y‖ ≤ B * Real.exp (-(κ * (zdist2 L (x - y) : ℝ))))
    (hE : ∀ d x y, ‖E d x y‖ ≤ B * Real.exp (-(κ * (zdist2 L (x - y) : ℝ)))) :
    ‖treeValW L F a M E‖ ≤ ((L * L : ℕ) : ℝ) ^ (n * n) * B ^ (n + n * n) *
        Real.exp (-(κ * (maxDist L a : ℝ))) := by
  have hB0 : 0 ≤ B := by linarith
  have hnn : F.card ≤ n * n := by
    have := card_le_univ F
    simpa using this
  have hN : (nodes F).card ≤ n * n := by
    have := card_le_univ (nodes F)
    simpa using this
  set X : ℝ := B ^ (n + F.card) * Real.exp (-(κ * (maxDist L a : ℝ))) with hX
  have hpt : ∀ b : ↥(nodes F) → Z2 L,
      ‖(∏ v : Fin n, M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)) *
        ∏ d : ↥F, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)‖
        ≤ X := by
    intro b
    obtain ⟨β, hβ⟩ : ∃ β : Fin n × Fin n → Z2 L, ∀ d (h : d ∈ nodes F), b ⟨d, h⟩ = β d :=
      ⟨fun d => if h : d ∈ nodes F then b ⟨d, h⟩ else 0, fun d h => by simp [h]⟩
    set Ls := ∑ v, zdist2 L (a v - β (leafPar F v))
    set Es := ∑ e ∈ F, zdist2 L (β e - β (nodePar F e))
    have hmax : maxDist L a ≤ Ls + Es := by
      refine Finset.sup_le fun p _ => ?_
      exact (dist_bounds hF hn a β p.1).1 p.2
    have hL : ∏ v : Fin n, ‖M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)‖
        ≤ B ^ n * Real.exp (-(κ * (Ls : ℝ))) := by
      calc ∏ v : Fin n, ‖M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)‖
          ≤ ∏ v : Fin n, (B * Real.exp (-(κ * (zdist2 L (a v - β (leafPar F v)) : ℝ)))) := by
            refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
            rw [hβ]; exact hM _ _ _
        _ = B ^ n * Real.exp (-(κ * (Ls : ℝ))) := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← Real.exp_sum]
            congr 2
            simp only [Ls, Nat.cast_sum, mul_sum, sum_neg_distrib]
    have hE' : ∏ d : ↥F, ‖E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)‖
        ≤ B ^ F.card * Real.exp (-(κ * (Es : ℝ))) := by
      calc ∏ d : ↥F, ‖E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)‖
          ≤ ∏ d : ↥F, (B * Real.exp
              (-(κ * (zdist2 L (β d.1 - β (nodePar F d.1)) : ℝ)))) := by
            refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun d _ => ?_
            rw [hβ, hβ]; exact hE _ _ _
        _ = B ^ F.card * Real.exp (-(κ * (Es : ℝ))) := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_coe, ← Real.exp_sum]
            congr 2
            rw [sum_coe_sort F (fun e => -(κ * (zdist2 L (β e - β (nodePar F e)) : ℝ)))]
            simp only [Es, Nat.cast_sum, mul_sum, sum_neg_distrib]
    have hexp : Real.exp (-(κ * (Ls : ℝ))) * Real.exp (-(κ * (Es : ℝ)))
        ≤ Real.exp (-(κ * (maxDist L a : ℝ))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : (maxDist L a : ℝ) ≤ (Ls : ℝ) + Es := by exact_mod_cast hmax
      have h2 : κ * (maxDist L a : ℝ) ≤ κ * ((Ls : ℝ) + Es) :=
        mul_le_mul_of_nonneg_left h1 hκ
      linarith
    rw [norm_mul, norm_prod, norm_prod]
    calc _ ≤ (B ^ n * Real.exp (-(κ * (Ls : ℝ)))) * (B ^ F.card * Real.exp (-(κ * (Es : ℝ)))) :=
          mul_le_mul hL hE' (prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      _ = B ^ (n + F.card) * (Real.exp (-(κ * (Ls : ℝ))) * Real.exp (-(κ * (Es : ℝ)))) := by
          ring
      _ ≤ B ^ (n + F.card) * Real.exp (-(κ * (maxDist L a : ℝ))) := by gcongr
  have hcard : Fintype.card (↥(nodes F) → Z2 L) = (L * L) ^ (nodes F).card := by
    rw [Fintype.card_fun, Fintype.card_coe]
    simp [Z2, Fintype.card_prod, ZMod.card]
  rw [treeValW]
  calc _ ≤ ∑ b : ↥(nodes F) → Z2 L, ‖(∏ v : Fin n, M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)) *
        ∏ d : ↥F, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _b : ↥(nodes F) → Z2 L, X := sum_le_sum fun b _ => hpt b
    _ = (((L * L : ℕ) : ℝ) ^ (nodes F).card) * X := by
        rw [sum_const, card_univ, hcard, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((L * L : ℕ) : ℝ) ^ (n * n) * B ^ (n + n * n) * Real.exp (-(κ * (maxDist L a : ℝ))) := by
        have hLL : (1 : ℝ) ≤ ((L * L : ℕ) : ℝ) := by
          have : 1 ≤ L * L := Nat.mul_pos (NeZero.pos L) (NeZero.pos L)
          exact_mod_cast this
        have h1 : ((L * L : ℕ) : ℝ) ^ (nodes F).card ≤ ((L * L : ℕ) : ℝ) ^ (n * n) :=
          pow_le_pow_right₀ hLL hN
        have h2 : B ^ (n + F.card) ≤ B ^ (n + n * n) :=
          pow_le_pow_right₀ hB (by omega)
        have h3 : 0 ≤ Real.exp (-(κ * (maxDist L a : ℝ))) := (Real.exp_pos _).le
        calc ((L * L : ℕ) : ℝ) ^ (nodes F).card * X
            = ((L * L : ℕ) : ℝ) ^ (nodes F).card * B ^ (n + F.card) *
                Real.exp (-(κ * (maxDist L a : ℝ))) := by rw [hX]; ring
          _ ≤ ((L * L : ℕ) : ℝ) ^ (n * n) * B ^ (n + n * n) *
                Real.exp (-(κ * (maxDist L a : ℝ))) := by gcongr

end TreeBound

/-! ## 5. The edge kernels in the far region

For `‖ξ‖ = u < 1` and `ℓ_u < L`: `|1 - ξ| ≥ 1 - u`, so `κ_ξ ≥ √(1-u)`, `ℓ̂(ξ) = κ_ξ⁻¹ ≤ ℓ_u`
and the prefactor `(κ_ξ² ℓ̂(ξ)²)⁻¹` of property 5 is `1`; the bulk gap `gapK` is not needed. -/

section Edges

variable {L : ℕ} [NeZero L]

private theorem kcalDecay_norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖mSig E s‖ = 1 := by
  cases s <;> simp [mSig, Gauss.norm_spectralM hE]

private theorem kcalDecay_norm_xi {E u : ℝ} (hE : |E| ≤ 2) (hu : 0 ≤ u) (s s' : Bool) :
    ‖(u : ℂ) * (mSig E s * mSig E s')‖ = u := by
  rw [norm_mul, norm_mul, kcalDecay_norm_mSig hE, kcalDecay_norm_mSig hE, Complex.norm_real,
    Real.norm_of_nonneg hu, mul_one, mul_one]

/-- Property 5 (`norm_Theta_apply_le_prop5`) in the far region `ℓ_u < L`, for `‖ξ‖ = u`. -/
private theorem kcalDecay_theta_bound (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hℓ : Path.ellT L u < L) {ξ : ℂ} (hξ : ‖ξ‖ = u) (x y : Z2 L) :
    ‖Theta L ξ x y‖ ≤ 180 * 40002 ^ 2 * (1 + Real.log L) *
      Real.exp (-(1 / (20000 * Path.ellT L u) * (zdist2 L (x - y) : ℝ))) := by
  have hξ1 : ‖ξ‖ < 1 := hξ ▸ hu1
  have h5 := norm_Theta_apply_le_prop5 L hL ξ hξ1 x y
  have h1u : 0 < 1 - u := by linarith
  set s := Real.sqrt (1 - u) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 h1u
  have hkξ : s ≤ kappa ξ := by
    unfold kappa
    apply Real.sqrt_le_sqrt
    have := norm_sub_norm_le (1 : ℂ) ξ
    rw [norm_one, hξ] at this
    linarith
  have hkpos : 0 < kappa ξ := lt_of_lt_of_le hspos hkξ
  have hs1L : 1 / s < (L : ℝ) := by
    unfold Path.ellT at hℓ
    rcases min_lt_iff.1 hℓ with h | h
    · exact h
    · exact absurd h (lt_irrefl _)
  have hell : Path.ellT L u = 1 / s := by
    unfold Path.ellT
    exact min_eq_left hs1L.le
  have hinv : (kappa ξ)⁻¹ ≤ 1 / s := by
    rw [one_div]
    exact inv_anti₀ hspos hkξ
  have hℓξ : ellhat L ξ = (kappa ξ)⁻¹ := min_eq_left (hinv.trans hs1L.le)
  have hpre : ((kappa ξ) ^ 2 * (ellhat L ξ) ^ 2)⁻¹ = 1 := by
    rw [hℓξ, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hkpos.ne'), inv_one]
  have hℓpos : 0 < ellhat L ξ := by rw [hℓξ]; exact inv_pos.2 hkpos
  have hz : (0 : ℝ) ≤ (zdist2 L (x - y) : ℝ) := Nat.cast_nonneg _
  have hle : ellhat L ξ ≤ Path.ellT L u := by rw [hℓξ, hell]; exact hinv
  have hexp : Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellhat L ξ)) ≤
      Real.exp (-(1 / (20000 * Path.ellT L u) * (zdist2 L (x - y) : ℝ))) := by
    apply Real.exp_le_exp.2
    have h20 : (0 : ℝ) < 20000 * ellhat L ξ := by positivity
    have hd : (zdist2 L (x - y) : ℝ) / (20000 * Path.ellT L u) ≤
        (zdist2 L (x - y) : ℝ) / (20000 * ellhat L ξ) :=
      div_le_div_of_nonneg_left hz h20 (by linarith)
    have e1 : 1 / (20000 * Path.ellT L u) * (zdist2 L (x - y) : ℝ) =
        (zdist2 L (x - y) : ℝ) / (20000 * Path.ellT L u) := by ring
    rw [e1, neg_div]
    linarith
  rw [hpre, mul_one] at h5
  refine h5.trans ?_
  have hC : 0 ≤ 180 * 40002 ^ 2 * (1 + Real.log L) := by
    have := Real.log_natCast_nonneg L
    positivity
  exact mul_le_mul_of_nonneg_left hexp hC

/-- The constant `B` of the edge bounds: `180·40002²(1 + log L) + 1 ≥ 1`. -/
private theorem kcalDecay_B_ge_one (L : ℕ) : 1 ≤ 180 * 40002 ^ 2 * (1 + Real.log L) + 1 := by
  have := Real.log_natCast_nonneg L
  nlinarith

/-- The leaf-edge bound: `|Θ_ξ(x,y)| ≤ B e^{-κ' |x-y|_L}`, `κ' = 1/(20000 ℓ_u)`. -/
private theorem kcalDecay_leaf_bound (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hℓ : Path.ellT L u < L) {ξ : ℂ} (hξ : ‖ξ‖ = u) (x y : Z2 L) :
    ‖Theta L ξ x y‖ ≤ (180 * 40002 ^ 2 * (1 + Real.log L) + 1) *
      Real.exp (-(1 / (20000 * Path.ellT L u) * (zdist2 L (x - y) : ℝ))) := by
  refine (kcalDecay_theta_bound hL hu0 hu1 hℓ hξ x y).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- The internal-edge bound: `|(Θ_ξ - 1)(x,y)| ≤ B e^{-κ' |x-y|_L}`. -/
private theorem kcalDecay_internal_bound (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hℓ : Path.ellT L u < L) {ξ : ℂ} (hξ : ‖ξ‖ = u) (x y : Z2 L) :
    ‖(Theta L ξ - 1) x y‖ ≤ (180 * 40002 ^ 2 * (1 + Real.log L) + 1) *
      Real.exp (-(1 / (20000 * Path.ellT L u) * (zdist2 L (x - y) : ℝ))) := by
  have hT := kcalDecay_theta_bound hL hu0 hu1 hℓ hξ x y
  rw [Matrix.sub_apply]
  by_cases hxy : x = y
  · subst hxy
    have h0 : (zdist2 L (x - x) : ℝ) = 0 := by simp
    rw [h0] at hT ⊢
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, Matrix.one_apply_eq] at hT ⊢
    have h2 := norm_sub_le (Theta L ξ x x) (1 : ℂ)
    rw [norm_one] at h2
    linarith
  · rw [Matrix.one_apply_ne hxy, sub_zero]
    refine hT.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end Edges

/-! ## 6. The primitive loop `𝒦` for `k ≥ 3` in the far region -/

section KcalFar

variable {L : ℕ} [NeZero L]

/-- The fibres `TSPlong n σ π` partition `TSP n`. -/
private theorem kcalDecay_sum_TSPlong {n : ℕ} {M : Type*} [AddCommMonoid M] (σ : Fin n → Bool)
    (f : Finset (Fin n × Fin n) → M) :
    ∑ π ∈ (diagonals n).powerset, ∑ F ∈ TSPlong n σ π, f F = ∑ F ∈ TSP n, f F := by
  refine sum_fiberwise_of_maps_to (fun F hF => ?_) f
  rw [mem_powerset]
  have hF' := (mem_filter.1 hF).1
  exact (filter_subset _ _).trans (mem_powerset.1 hF')

/-- Crude count of the trees: `|T_SP(n)| ≤ 2^{n²}` (`T_SP(n)` is a set of subsets of the
`≤ n²` pairs). -/
private theorem kcalDecay_card_TSP (n : ℕ) : (TSP n).card ≤ 2 ^ (n * n) := by
  have h1 : (TSP n).card ≤ ((diagonals n).powerset).card := card_le_card (filter_subset _ _)
  rw [card_powerset] at h1
  have h2 : (diagonals n).card ≤ n * n := by
    have := card_le_univ (diagonals n)
    simpa using this
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)

/-- **`𝒦` at far labels, `k ≥ 3`, deterministic** (`Kn`, [50] (3.5) in `d = 2`): with `B` the
kernel constant and `κ' = 1/(20000 ℓ_u)`,
`|𝒦_{u,σ,a}| ≤ 2^{k²} (L²)^{k²} B^{k+k²} e^{-κ' maxDist a}`, when `ℓ_u < L`. -/
private theorem kcalDecay_Kcal_far (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) {E u : ℝ} (hE : |E| ≤ 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hℓ : Path.ellT L u < L) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    ‖Kcal L W E u (loopOf L σ a)‖ ≤ 2 ^ (k * k) * (((L * L : ℕ) : ℝ) ^ (k * k) *
      (180 * 40002 ^ 2 * (1 + Real.log L) + 1) ^ (k + k * k) *
        Real.exp (-(1 / (20000 * Path.ellT L u) * (maxDist L a : ℝ)))) := by
  rw [Kcal_eq_sum_Kpi L W E u k hk σ a]
  simp only [Kpi]
  rw [kcalDecay_sum_TSPlong σ (fun F => treeValG L (mSig E) u σ a F)]
  have hℓpos : 0 < Path.ellT L u := (Path.ellT_pos_le (by omega) hu1).1
  set B : ℝ := 180 * 40002 ^ 2 * (1 + Real.log L) + 1 with hB
  set κ' : ℝ := 1 / (20000 * Path.ellT L u) with hκ'
  have hκ0 : 0 ≤ κ' := by positivity
  set X : ℝ := ((L * L : ℕ) : ℝ) ^ (k * k) * B ^ (k + k * k) *
    Real.exp (-(κ' * (maxDist L a : ℝ))) with hX
  have hB1 : 1 ≤ B := kcalDecay_B_ge_one L
  have hX0 : 0 ≤ X := by positivity
  have htree : ∀ F ∈ TSP k, ‖treeValG L (mSig E) u σ a F‖ ≤ X := by
    intro F hF
    exact kcalDecay_tree_bound (isTSPf_of_mem hF) (by omega) a _ _ hB1 hκ0
      (fun v x y => kcalDecay_leaf_bound hL hu0 hu1 hℓ
        (ξ := (u : ℂ) * (mSig E (σ v) * mSig E (σ (v + 1)))) (kcalDecay_norm_xi hE hu0 _ _) x y)
      (fun d x y => kcalDecay_internal_bound hL hu0 hu1 hℓ
        (ξ := (u : ℂ) * (mSig E (σ d.1.1) * mSig E (σ d.1.2))) (kcalDecay_norm_xi hE hu0 _ _) x y)
  have hW' : ‖((W : ℂ) ^ 2)⁻¹ ^ (k - 1)‖ ≤ 1 := by
    rw [norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
    have h1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ h1))
  have hprod : ‖∏ i : Fin k, mSig E (σ i)‖ = 1 := by
    rw [norm_prod]
    exact prod_eq_one fun i _ => kcalDecay_norm_mSig hE _
  have hsum : ‖∑ F ∈ TSP k, treeValG L (mSig E) u σ a F‖ ≤ 2 ^ (k * k) * X := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum htree).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have h2 : ((TSP k).card : ℝ) ≤ 2 ^ (k * k) := by exact_mod_cast kcalDecay_card_TSP k
    exact mul_le_mul_of_nonneg_right h2 hX0
  rw [norm_mul, norm_mul, hprod, mul_one]
  calc ‖((W : ℂ) ^ 2)⁻¹ ^ (k - 1)‖ * ‖∑ F ∈ TSP k, treeValG L (mSig E) u σ a F‖
      ≤ 1 * (2 ^ (k * k) * X) := mul_le_mul hW' hsum (norm_nonneg _) zero_le_one
    _ = 2 ^ (k * k) * X := one_mul _

end KcalFar

/-! ## 7. The primitive loop `𝒦` for `k = 2` (`(Kn2sol)`) in the far region -/

section KcalTwo

variable {L : ℕ} [NeZero L]

/-- `max_{i,j} |a_i - a_j|_L ≤ |a₁ - a₂|_L` for `k = 2`. -/
private theorem kcalDecay_maxDist_two_le (a : Fin 2 → Z2 L) :
    maxDist L a ≤ zdist2 L (a 0 - a 1) := by
  refine Finset.sup_le fun p _ => ?_
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> simp [zdist2_symm]

/-- `𝒦` at far labels, `k = 2`: `|𝒦_{u,σ,(a₁,a₂)}| = W⁻²|Θ_ξ(a₁,a₂)| ≤ B e^{-κ' maxDist a}`, by
`maxDist a ≤ |a₁-a₂|_L`. -/
private theorem kcalDecay_Kcal_two_far (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) {E u : ℝ}
    (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hℓ : Path.ellT L u < L) (σ : Fin 2 → Bool)
    (a : Fin 2 → Z2 L) :
    ‖Kcal L W E u (loopOf L σ a)‖ ≤ (180 * 40002 ^ 2 * (1 + Real.log L) + 1) *
      Real.exp (-(1 / (20000 * Path.ellT L u) * (maxDist L a : ℝ))) := by
  have hI : loopOf L σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [loopOf, List.ofFn_succ]
  rw [hI, Kcal_two]
  have hℓpos : 0 < Path.ellT L u := (Path.ellT_pos_le (by omega) hu1).1
  have hκ0 : 0 ≤ 1 / (20000 * Path.ellT L u) := by positivity
  have hW' : ‖((W : ℂ) ^ 2)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
    have h1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  have hm : ‖mSig E (σ 0) * mSig E (σ 1)‖ = 1 := by
    rw [norm_mul, kcalDecay_norm_mSig hE, kcalDecay_norm_mSig hE, mul_one]
  have hT := kcalDecay_leaf_bound hL hu0 hu1 hℓ
    (ξ := (u : ℂ) * (mSig E (σ 0) * mSig E (σ 1))) (kcalDecay_norm_xi hE hu0 _ _) (a 0) (a 1)
  have hmd : (maxDist L a : ℝ) ≤ (zdist2 L (a 0 - a 1) : ℝ) := by
    exact_mod_cast kcalDecay_maxDist_two_le a
  have hexp : Real.exp (-(1 / (20000 * Path.ellT L u) * (zdist2 L (a 0 - a 1) : ℝ))) ≤
      Real.exp (-(1 / (20000 * Path.ellT L u) * (maxDist L a : ℝ))) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hmd hκ0
    linarith
  have hB0 : 0 ≤ 180 * 40002 ^ 2 * (1 + Real.log L) + 1 := by
    have := kcalDecay_B_ge_one L
    linarith
  rw [norm_mul, norm_mul, hm, mul_one]
  calc ‖((W : ℂ) ^ 2)⁻¹‖ * ‖Theta L ((u : ℂ) * (mSig E (σ 0) * mSig E (σ 1))) (a 0) (a 1)‖
      ≤ 1 * ((180 * 40002 ^ 2 * (1 + Real.log L) + 1) *
          Real.exp (-(1 / (20000 * Path.ellT L u) * (maxDist L a : ℝ)))) := by
        refine mul_le_mul hW' (hT.trans ?_) (norm_nonneg _) zero_le_one
        exact mul_le_mul_of_nonneg_left hexp hB0
    _ = _ := one_mul _

end KcalTwo

/-! ## 8. The asymptotic absorption -/

/-- `A N^Q N^D e^{-N^s/20000} ≤ 1` eventually in `N`, for `s > 0`. -/
private theorem kcalDecay_eventually (A : ℝ) (Q : ℕ) (D s : ℝ) (hs : 0 < s) :
    ∀ᶠ N : ℕ in Filter.atTop,
      A * (N : ℝ) ^ Q * (N : ℝ) ^ D * Real.exp (-((N : ℝ) ^ s) / 20000) ≤ 1 := by
  have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ s) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (((Q : ℝ) + D) / s) (1 / 20000)
    (by norm_num)
  have h3 : Filter.Tendsto (fun N : ℕ => A * (((N : ℝ) ^ s) ^ (((Q : ℝ) + D) / s) *
      Real.exp (-(1 / 20000) * (N : ℝ) ^ s))) Filter.atTop (nhds (A * 0)) :=
    (h2.comp h1).const_mul A
  rw [mul_zero] at h3
  filter_upwards [Filter.eventually_ge_atTop 1, h3.eventually (gt_mem_nhds one_pos)] with N hN1 hN3
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have e1 : ((N : ℝ) ^ s) ^ (((Q : ℝ) + D) / s) = (N : ℝ) ^ Q * (N : ℝ) ^ D := by
    rw [← Real.rpow_mul hN0.le, mul_div_cancel₀ _ hs.ne', Real.rpow_add hN0, Real.rpow_natCast]
  have e2 : -(1 / 20000 : ℝ) * (N : ℝ) ^ s = -((N : ℝ) ^ s) / 20000 := by ring
  simp only [e1, e2] at hN3
  linarith [hN3, show A * ((N : ℝ) ^ Q * (N : ℝ) ^ D * Real.exp (-((N : ℝ) ^ s) / 20000)) =
    A * (N : ℝ) ^ Q * (N : ℝ) ^ D * Real.exp (-((N : ℝ) ^ s) / 20000) by ring]

end RBM.KLoop

namespace RBM.Ind

open Filter RBM.KLoop

/-- **`kcalDecay`** (the statement `KcalDecay`): the fast decay of the primitive
loop `𝒦` at far labels, deterministic, eventually in `N`.  Proof: `k = 1` has `maxDist = 0`; in the
far region `ℓ_u W^τ ≤ maxDist ≤ L` forces `ℓ_u < L`, hence `ℓ̂(ξ) = κ_ξ⁻¹ ≤ ℓ_u` for every edge
parameter `‖ξ‖ = u`, and property 5 gives every edge kernel `≤ B e^{-|x-y|_L/(20000 ℓ_u)}`; the tree
representation `Kn` and the path bound `dist_bounds` give `|𝒦| ≤ A N^Q e^{-W^τ/20000}` with
`A = 2^{k²}(180·40002²+1)^{k+k²}`, `Q = 2k²+k`, and this is `≤ W^{-D}` eventually. -/
theorem kcalDecay (κ : ℝ) : KcalDecay κ := by
  intro hκ 𝔠 h𝔠 k hk τ D hτ hD
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = 180 * 40002 ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 ^ (k * k) * C₀ ^ (k + k * k) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = 2 * (k * k) + k := ⟨_, rfl⟩
  have hC₀1 : 1 ≤ C₀ := by rw [hC₀]; norm_num
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  filter_upwards [kcalDecay_eventually A Q D (𝔠 * τ) (mul_pos h𝔠 hτ), eventually_ge_atTop 2]
    with N hN hN2
  intro L W _ _ hL hNLW hNW E hE u hu0 hu1 σ a hfar
  have hE2 : |E| ≤ 2 := by linarith [abs_nonneg E]
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have h1N : (1 : ℝ) < (N : ℝ) ^ 𝔠 := Real.one_lt_rpow (by linarith) h𝔠
  have hW1 : (1 : ℝ) < W := lt_of_lt_of_le h1N hNW
  have hW1' : 1 ≤ W := by exact_mod_cast hW1.le
  have hWpos : (0 : ℝ) < W := by linarith
  have hWτ : 1 < (W : ℝ) ^ τ := Real.one_lt_rpow hW1 hτ
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  obtain ⟨hℓpos, hℓle⟩ := Path.ellT_pos_le (show 1 ≤ L by omega) hu1
  have hWpos' : 0 < W := Nat.pos_of_ne_zero (NeZero.ne W)
  have hLpos' : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hL2 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ hLpos'
  have hW2 : 1 ≤ W ^ 2 := Nat.one_le_pow _ _ hWpos'
  have hWN' : W ≤ N :=
    calc W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) W
      _ = W ^ 2 * 1 := (mul_one _).symm
      _ ≤ W ^ 2 * L ^ 2 := Nat.mul_le_mul_left _ hL2
      _ = N := hNLW
  have hLLN' : L * L ≤ N :=
    calc L * L = L ^ 2 := (sq L).symm
      _ = 1 * L ^ 2 := (one_mul _).symm
      _ ≤ W ^ 2 * L ^ 2 := Nat.mul_le_mul_right _ hW2
      _ = N := hNLW
  have hWN : (W : ℝ) ≤ N := by exact_mod_cast hWN'
  have hLLN : ((L * L : ℕ) : ℝ) ≤ N := by exact_mod_cast hLLN'
  have hLN : (L : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_mul_self L) hLLN'
  -- the far-region estimate `|𝒦| ≤ A N^Q e^{-W^τ/20000}`
  have key : ‖KLoop.Kcal L W E u (Path.loopOf σ a)‖ ≤
      A * (N : ℝ) ^ Q * Real.exp (-((W : ℝ) ^ τ) / 20000) := by
    -- `maxDist ≤ L`
    have hmaxL : (maxDist L a : ℝ) ≤ L := by
      have : maxDist L a ≤ L := Finset.sup_le fun p _ => zdist2_le_L L _
      exact_mod_cast this
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · -- `k = 1`: `maxDist = 0`, the premise fails
      exfalso
      have hk1 : k = 1 := by omega
      subst hk1
      have hmd : maxDist L a = 0 := by
        refine Nat.le_zero.1 (Finset.sup_le fun p _ => ?_)
        have : p.1 = p.2 := Subsingleton.elim _ _
        simp [this]
      rw [hmd] at hfar
      have : 0 < Path.ellT L u * (W : ℝ) ^ τ := mul_pos hℓpos (by linarith)
      simp at hfar
      linarith
    · -- `k ≥ 2`: the premise forces `ℓ_u < L`
      have hℓL : Path.ellT L u < L := by
        refine lt_of_le_of_ne hℓle fun h => ?_
        rw [h] at hfar
        have : (L : ℝ) * (W : ℝ) ^ τ ≤ L * 1 := by linarith
        have := le_of_mul_le_mul_left this hLpos
        linarith
      -- `κ' maxDist ≥ W^τ / 20000`
      have hκ' : ((W : ℝ) ^ τ) / 20000 ≤ 1 / (20000 * Path.ellT L u) * (maxDist L a : ℝ) := by
        have h1 : 1 / (20000 * Path.ellT L u) * (Path.ellT L u * (W : ℝ) ^ τ) ≤
            1 / (20000 * Path.ellT L u) * (maxDist L a : ℝ) :=
          mul_le_mul_of_nonneg_left hfar (by positivity)
        have h2 : 1 / (20000 * Path.ellT L u) * (Path.ellT L u * (W : ℝ) ^ τ) =
            ((W : ℝ) ^ τ) / 20000 := by
          field_simp
        linarith
      have hexp : Real.exp (-(1 / (20000 * Path.ellT L u) * (maxDist L a : ℝ))) ≤
          Real.exp (-((W : ℝ) ^ τ) / 20000) := by
        apply Real.exp_le_exp.2
        rw [neg_div]
        linarith
      -- the kernel constant `B ≤ C₀ N`
      have hBN : 180 * 40002 ^ 2 * (1 + Real.log L) + 1 ≤ C₀ * N := by
        have hlog : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
        have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
        rw [hC₀]
        nlinarith
      have hB0 : 0 ≤ 180 * 40002 ^ 2 * (1 + Real.log L) + 1 := by
        have := kcalDecay_B_ge_one L
        linarith
      have hloop : Path.loopOf σ a = KLoop.loopOf L σ a := rfl
      rw [hloop]
      rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · -- `k = 2`
        have hk2' : k = 2 := by omega
        subst hk2'
        refine (kcalDecay_Kcal_two_far hL W hW1' hE2 hu0 hu1 hℓL σ a).trans ?_
        have hpow : (N : ℝ) ≤ (N : ℝ) ^ Q := by
          refine le_self_pow₀ (by linarith) ?_
          omega
        have hCA : C₀ ≤ A := by
          rw [hA]
          have h1 : C₀ ≤ C₀ ^ (2 + 2 * 2) := le_self_pow₀ hC₀1 (by norm_num)
          have h2 : (1 : ℝ) ≤ 2 ^ (2 * 2) := one_le_pow₀ (by norm_num)
          nlinarith
        calc (180 * 40002 ^ 2 * (1 + Real.log L) + 1) *
              Real.exp (-(1 / (20000 * Path.ellT L u) * (maxDist L a : ℝ)))
            ≤ (C₀ * N) * Real.exp (-((W : ℝ) ^ τ) / 20000) := by gcongr
          _ ≤ A * (N : ℝ) ^ Q * Real.exp (-((W : ℝ) ^ τ) / 20000) := by
            have : C₀ * (N : ℝ) ≤ A * (N : ℝ) ^ Q :=
              mul_le_mul hCA hpow hN0.le hA0
            exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      · -- `k ≥ 3`
        have : NeZero k := ⟨by omega⟩
        refine (kcalDecay_Kcal_far hL W hW1' hE2 hu0 hu1 hℓL hk3 σ a).trans ?_
        calc 2 ^ (k * k) * (((L * L : ℕ) : ℝ) ^ (k * k) *
              (180 * 40002 ^ 2 * (1 + Real.log L) + 1) ^ (k + k * k) *
                Real.exp (-(1 / (20000 * Path.ellT L u) * (maxDist L a : ℝ))))
            ≤ 2 ^ (k * k) * (((N : ℝ)) ^ (k * k) * (C₀ * N) ^ (k + k * k) *
                Real.exp (-((W : ℝ) ^ τ) / 20000)) := by gcongr
          _ = A * (N : ℝ) ^ Q * Real.exp (-((W : ℝ) ^ τ) / 20000) := by
            rw [hA, hQ]
            have : (N : ℝ) ^ (2 * (k * k) + k) = (N : ℝ) ^ (k * k) * (N : ℝ) ^ (k + k * k) := by
              rw [← pow_add]; congr 1; ring
            rw [this, mul_pow]
            ring
  -- absorb into `W^{-D}`
  have hWD : (W : ℝ) ^ D ≤ (N : ℝ) ^ D := Real.rpow_le_rpow hWpos.le hWN hD.le
  have hNs : (N : ℝ) ^ (𝔠 * τ) ≤ (W : ℝ) ^ τ := by
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hNW hτ.le
  have hexp : Real.exp (-((W : ℝ) ^ τ) / 20000) ≤ Real.exp (-((N : ℝ) ^ (𝔠 * τ)) / 20000) := by
    apply Real.exp_le_exp.2
    linarith
  have hWDpos : 0 < (W : ℝ) ^ D := Real.rpow_pos_of_pos hWpos D
  rw [Real.rpow_neg hWpos.le, ← one_div, le_div_iff₀ hWDpos]
  calc ‖KLoop.Kcal L W E u (Path.loopOf σ a)‖ * (W : ℝ) ^ D
      ≤ (A * (N : ℝ) ^ Q * Real.exp (-((W : ℝ) ^ τ) / 20000)) * (W : ℝ) ^ D :=
        mul_le_mul_of_nonneg_right key hWDpos.le
    _ ≤ (A * (N : ℝ) ^ Q * Real.exp (-((N : ℝ) ^ (𝔠 * τ)) / 20000)) * (N : ℝ) ^ D := by
        have hAN : 0 ≤ A * (N : ℝ) ^ Q := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hAN) hWD hWDpos.le
          (mul_nonneg hAN (Real.exp_pos _).le)
    _ = A * (N : ℝ) ^ Q * (N : ℝ) ^ D * Real.exp (-((N : ℝ) ^ (𝔠 * τ)) / 20000) := by ring
    _ ≤ 1 := hN

end RBM.Ind
