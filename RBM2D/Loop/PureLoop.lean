/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.Kcal
import RBM2D.Loop.LatticeCount

/-!
# The short-range self-energy in `≺` form

Theorem (namespace `RBM.KLoop`):

* `SigmaPi_empty_shortRange_prec` : `(res_SIGempdd)`.

It is conditional on `Prop5Hyp κ c` (property 5 of `lem_propTH`, a `≺` bound).  The
argument parallels the one-dimensional case, with `ZMod L ↦ Z2 L`,
`W⁻¹ ↦ (W²)⁻¹` per edge, and the deterministic decay of `Θ` replaced by `Prop5Hyp`.  Two
differences: the leaf-to-leaf distance is bounded by the total edge length (not twice it),
which gives the rate `c √c_κ / 2` (instead of `/ 4`), and the bulk gap `c_κ ≤ |1 - t m²|` is
proved directly.
-/

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

This sharpens the bound that routes every pair of leaves through the root and only gives
`2 ×` the total length. -/

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

/-! ## 4. Trees with exponentially decaying edges decay

The statement is as in the one-dimensional case, with `ZMod L ↦ Z2 L`,
`sum_exp_zdist_le ↦ sum_exp_le` and the sharper rate `κ / 2` (instead of `κ / 4`)
from the path bound of section 3. -/

section TreeBound

variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]

private theorem one_le_one_add_sq {lam : ℝ} (hlam : 0 < lam) : 1 ≤ (1 + 2 / lam) ^ 2 := by
  have : 0 ≤ 2 / lam := by positivity
  nlinarith

private theorem tree_bound {F : Finset (Fin n × Fin n)} (hF : IsTSPf F) (hn : 2 ≤ n)
    (a : Fin n → Z2 L) (M : Fin n → Matrix (Z2 L) (Z2 L) ℂ)
    (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) {B κ : ℝ} (hB : 1 ≤ B) (hκ : 0 < κ)
    (hM : ∀ v x y, ‖M v x y‖ ≤ B * Real.exp (-(κ * (zdist2 L (x - y) : ℝ))))
    (hE : ∀ d x y, ‖E d x y‖ ≤ B * Real.exp (-(κ * (zdist2 L (x - y) : ℝ)))) (i j : Fin n) :
    ‖treeValW L F a M E‖ ≤ B ^ (n + n * n) *
      ((1 + 2 / (κ / (2 * ((n * n : ℕ) : ℝ)))) ^ 2) ^ (n * n) *
        Real.exp (-(κ / 2 * (zdist2 L (a i - a j) : ℝ))) := by
  have hnn : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
    have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
  set lam := κ / (2 * ((n * n : ℕ) : ℝ)) with hlam_def
  have hlam : 0 < lam := by positivity
  set S := (1 + 2 / lam) ^ 2 with hS
  have hS1 : 1 ≤ S := one_le_one_add_sq hlam
  set N := (nodes F).card
  have hN : N ≤ n * n := by
    have := card_le_univ (nodes F)
    simpa using this
  have hFN : F.card ≤ N := card_le_card (subset_insert _ _)
  set g : Z2 L → ℝ := fun x => Real.exp (-(lam * (zdist2 L (a i - x) : ℝ)))
  set C0 := B ^ (n + F.card) * Real.exp (-(κ / 2 * (zdist2 L (a i - a j) : ℝ)))
  have hB0 : 0 ≤ B := by linarith
  have hpt : ∀ b : ↥(nodes F) → Z2 L,
      ‖(∏ v : Fin n, M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)) *
        ∏ d : ↥F, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)‖
        ≤ C0 * ∏ ν : ↥(nodes F), g (b ν) := by
    intro b
    obtain ⟨β, hβ⟩ : ∃ β : Fin n × Fin n → Z2 L, ∀ d (h : d ∈ nodes F), b ⟨d, h⟩ = β d :=
      ⟨fun d => if h : d ∈ nodes F then b ⟨d, h⟩ else 0, fun d h => by simp [h]⟩
    have hβ' : ∀ ν : ↥(nodes F), b ν = β ν.1 := fun ν => hβ ν.1 ν.2
    set Ls := ∑ v, zdist2 L (a v - β (leafPar F v))
    set Es := ∑ e ∈ F, zdist2 L (β e - β (nodePar F e))
    obtain ⟨hij, hnode⟩ := dist_bounds hF hn a β i
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
        ≤ Real.exp (-(κ / 2 * (zdist2 L (a i - a j) : ℝ))) * ∏ ν : ↥(nodes F), g (b ν) := by
      simp only [g, ← Real.exp_sum, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : (zdist2 L (a i - a j) : ℝ) ≤ (Ls : ℝ) + Es := by exact_mod_cast hij j
      have h2 : ∑ ν : ↥(nodes F), (zdist2 L (a i - b ν) : ℝ) ≤ N * ((Ls : ℝ) + Es) := by
        have : ∀ ν : ↥(nodes F), (zdist2 L (a i - b ν) : ℝ) ≤ (Ls : ℝ) + Es := by
          intro ν; rw [hβ']; exact_mod_cast hnode ν.1 ν.2
        calc _ ≤ ∑ _ν : ↥(nodes F), ((Ls : ℝ) + Es) := sum_le_sum fun ν _ => this ν
          _ = N * ((Ls : ℝ) + Es) := by rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      have h3 : (N : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hN
      have hD : (0 : ℝ) ≤ (Ls : ℝ) + Es := by positivity
      have h4 : lam * ∑ ν : ↥(nodes F), (zdist2 L (a i - b ν) : ℝ)
          ≤ κ / 2 * ((Ls : ℝ) + Es) := by
        calc _ ≤ lam * (((n * n : ℕ) : ℝ) * ((Ls : ℝ) + Es)) := by
              gcongr; exact h2.trans (by gcongr)
          _ = κ / 2 * ((Ls : ℝ) + Es) := by rw [hlam_def]; field_simp
      have h5 : κ / 2 * (zdist2 L (a i - a j) : ℝ) ≤ κ / 2 * ((Ls : ℝ) + Es) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h6 : ∑ ν : ↥(nodes F), -(lam * (zdist2 L (a i - b ν) : ℝ))
          = -(lam * ∑ ν : ↥(nodes F), (zdist2 L (a i - b ν) : ℝ)) := by
        rw [mul_sum, sum_neg_distrib]
      rw [h6]
      nlinarith
    rw [norm_mul, norm_prod, norm_prod]
    calc _ ≤ (B ^ n * Real.exp (-(κ * (Ls : ℝ)))) * (B ^ F.card * Real.exp (-(κ * (Es : ℝ)))) :=
          mul_le_mul hL hE' (prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      _ = B ^ (n + F.card) * (Real.exp (-(κ * (Ls : ℝ))) * Real.exp (-(κ * (Es : ℝ)))) := by
          ring
      _ ≤ B ^ (n + F.card) * (Real.exp (-(κ / 2 * (zdist2 L (a i - a j) : ℝ))) *
            ∏ ν : ↥(nodes F), g (b ν)) := by gcongr
      _ = C0 * ∏ ν : ↥(nodes F), g (b ν) := by ring
  have hsum : ∑ b : ↥(nodes F) → Z2 L, ∏ ν : ↥(nodes F), g (b ν) = (∑ x, g x) ^ N := by
    have h := Finset.prod_univ_sum (fun _ : ↥(nodes F) => (univ : Finset (Z2 L)))
      (fun _ x => g x)
    rw [Fintype.piFinset_univ] at h
    rw [← h, prod_const, card_univ, Fintype.card_coe]
  have hg : ∑ x, g x ≤ S := sum_exp_le L lam hlam (a i)
  have hg0 : 0 ≤ ∑ x, g x := sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hC0 : 0 ≤ C0 := by positivity
  rw [treeValW]
  calc _ ≤ ∑ b : ↥(nodes F) → Z2 L, C0 * ∏ ν : ↥(nodes F), g (b ν) :=
        (norm_sum_le _ _).trans (sum_le_sum fun b _ => hpt b)
    _ = C0 * (∑ x, g x) ^ N := by rw [← mul_sum, hsum]
    _ ≤ C0 * S ^ (n * n) := by
        gcongr
        exact (pow_le_pow_left₀ hg0 hg N).trans (pow_le_pow_right₀ hS1 hN)
    _ ≤ B ^ (n + n * n) * S ^ (n * n) * Real.exp (-(κ / 2 * (zdist2 L (a i - a j) : ℝ))) := by
        have : B ^ (n + F.card) ≤ B ^ (n + n * n) := pow_le_pow_right₀ hB (by omega)
        have hS0 : 0 ≤ S ^ (n * n) := by positivity
        calc C0 * S ^ (n * n) = B ^ (n + F.card) * S ^ (n * n) *
              Real.exp (-(κ / 2 * (zdist2 L (a i - a j) : ℝ))) := by ring
          _ ≤ _ := by gcongr

end TreeBound

/-! ## 5. The bulk gap `c_κ ≤ |1 - t m²|` and the edge bound from `Prop5Hyp`

The gap is proved directly (elementary algebra); the weaker bound `√k` would give the rate
`c κ^{1/4}` instead of `c √c_κ`. -/

section Gap

private theorem gapK_nonneg (κ : ℝ) : 0 ≤ gapK κ :=
  le_min zero_le_one (Real.sqrt_nonneg _)

private theorem gapK_le_one (κ : ℝ) : gapK κ ≤ 1 := min_le_left _ _

private theorem gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < gapK κ :=
  lt_min one_pos (Real.sqrt_pos.2 (by nlinarith))

private theorem gapK_sq_le {κ : ℝ} (hκ2 : κ ≤ 2) (hκ : 0 < κ) :
    gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ κ * (4 - κ) / 2 := by nlinarith
  calc gapK κ ^ 2 ≤ (Real.sqrt (κ * (4 - κ) / 2)) ^ 2 :=
        pow_le_pow_left₀ (gapK_nonneg κ) (min_le_right _ _) 2
    _ = κ * (4 - κ) / 2 := Real.sq_sqrt h0

/-- The bulk gap: `c_κ ≤ |1 - t m²|` for `t ≥ 0`, `|E| ≤ 2 - κ` (`m = m^{(E)}`). -/
private theorem gap_le_norm {κ : ℝ} (hκ : 0 < κ) {E t : ℝ} (hE : |E| ≤ 2 - κ) (ht : 0 ≤ t) :
    gapK κ ≤ ‖(1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2‖ := by
  have hE2 : |E| ≤ 2 := by linarith
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  set s := Real.sqrt (4 - E ^ 2) with hs_def
  have hs : s ^ 2 = 4 - E ^ 2 := Gauss.spectralM_sqrt_sq hE2
  have hre : (Gauss.spectralM E).re = -E / 2 := by simp [Gauss.spectralM]
  have him : (Gauss.spectralM E).im = s / 2 := Gauss.spectralM_im E
  have hzre : ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2).re
      = 1 - t * ((-E / 2) ^ 2 - (s / 2) ^ 2) := by
    simp [pow_two, Complex.mul_re, hre, him]
  have hzim : ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2).im
      = -(t * (2 * (-E / 2) * (s / 2))) := by
    simp only [pow_two, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_sub, hre, him]
    ring
  have hsq : ‖(1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2‖ ^ 2
      = 1 - t * (E ^ 2 - 2) + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    linear_combination (t / 2 + t ^ 2 * (8 + (s ^ 2 - (4 - E ^ 2))) / 16) * hs
  have hg0 := gapK_nonneg κ
  have hg1 : gapK κ ^ 2 ≤ 1 := pow_le_one₀ hg0 (gapK_le_one κ)
  have hg2 := gapK_sq_le hκ2 hκ
  have hmain : gapK κ ^ 2 ≤ 1 - t * (E ^ 2 - 2) + t ^ 2 := by
    by_cases hc : E ^ 2 ≤ 2
    · nlinarith [mul_nonneg ht (sub_nonneg.2 hc), sq_nonneg t]
    · have hc := not_le.1 hc
      have hy : E ^ 2 ≤ (2 - κ) ^ 2 := by
        rw [← sq_abs E]
        exact pow_le_pow_left₀ (abs_nonneg E) hE 2
      have hk4 : 0 ≤ 4 - (2 - κ) ^ 2 := by nlinarith
      have h1 : κ * (4 - κ) / 2 ≤ E ^ 2 * (4 - E ^ 2) / 4 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hy) (show 0 ≤ E ^ 2 + (2 - κ) ^ 2 - 4 by nlinarith),
          mul_nonneg hk4 (show 0 ≤ (2 - κ) ^ 2 - 2 by nlinarith)]
      nlinarith [sq_nonneg (t - (E ^ 2 / 2 - 1))]
  by_contra hlt
  have hlt := not_le.1 hlt
  have := norm_nonneg ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2)
  nlinarith

private theorem gap_le_norm_mSig {κ : ℝ} (hκ : 0 < κ) {E t : ℝ} (hE : |E| ≤ 2 - κ)
    (ht : 0 ≤ t) (s : Bool) : gapK κ ≤ ‖(1 : ℂ) - (t : ℂ) * mSig E s ^ 2‖ := by
  cases s
  · have h := gap_le_norm hκ hE ht
    have : (1 : ℂ) - (t : ℂ) * mSig E false ^ 2
        = (starRingEnd ℂ) ((1 : ℂ) - (t : ℂ) * Gauss.spectralM E ^ 2) := by
      simp [mSig]
    rw [this, Complex.norm_conj]
    exact h
  · simpa [mSig] using gap_le_norm hκ hE ht

/-- The right side of `Prop5Hyp` is at most `c_κ⁻¹ e^{-c √c_κ |x-y|}`:
`ℓ̂ ≤ c_κ^{-1/2}` and `|1-ξ| ℓ̂² ≥ c_κ`. -/
private theorem edge_rhs_le {L : ℕ} [NeZero L] {ξ : ℂ} {g c d : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hgξ : g ≤ ‖(1 : ℂ) - ξ‖) (hc : 0 < c) (hd : 0 ≤ d) (hL : 3 ≤ L) :
    Real.exp (-(c * d) / ellhat L ξ) / (‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2)
      ≤ g⁻¹ * Real.exp (-(c * Real.sqrt g * d)) := by
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hκξ : Real.sqrt g ≤ kappa ξ := Real.sqrt_le_sqrt hgξ
  have hκpos : 0 < kappa ξ := lt_of_lt_of_le hsg hκξ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hℓpos : 0 < ellhat L ξ := lt_min (inv_pos.2 hκpos) (by linarith)
  have hℓle : ellhat L ξ ≤ (Real.sqrt g)⁻¹ := (min_le_left _ _).trans (inv_anti₀ hsg hκξ)
  have hinv : Real.sqrt g * ellhat L ξ ≤ 1 := by
    calc Real.sqrt g * ellhat L ξ ≤ Real.sqrt g * (Real.sqrt g)⁻¹ :=
          mul_le_mul_of_nonneg_left hℓle hsg.le
      _ = 1 := mul_inv_cancel₀ hsg.ne'
  have hexp : c * Real.sqrt g * d ≤ c * d / ellhat L ξ := by
    rw [le_div_iff₀ hℓpos]
    have : 0 ≤ c * d := by positivity
    nlinarith
  have hkl : Real.sqrt g ≤ kappa ξ * ellhat L ξ := by
    rcases le_total (kappa ξ)⁻¹ (L : ℝ) with h | h
    · have : ellhat L ξ = (kappa ξ)⁻¹ := min_eq_left h
      rw [this, mul_inv_cancel₀ hκpos.ne']
      exact Real.sqrt_le_one.2 hg1 |>.trans_eq rfl
    · have : ellhat L ξ = L := min_eq_right h
      rw [this]
      nlinarith
  have hden : g ≤ ‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2 := by
    rw [← kappa_sq, ← mul_pow]
    calc g = Real.sqrt g ^ 2 := (Real.sq_sqrt hg.le).symm
      _ ≤ _ := pow_le_pow_left₀ hsg.le hkl 2
  have hden' : 0 < ‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2 := lt_of_lt_of_le hg hden
  calc Real.exp (-(c * d) / ellhat L ξ) / (‖(1 : ℂ) - ξ‖ * ellhat L ξ ^ 2)
      ≤ Real.exp (-(c * Real.sqrt g * d)) / g := by
        refine div_le_div₀ (Real.exp_pos _).le ?_ hg hden
        apply Real.exp_le_exp.2
        rw [neg_div]
        linarith
    _ = g⁻¹ * Real.exp (-(c * Real.sqrt g * d)) := by rw [div_eq_inv_mul]

/-- **The edge bound from `Prop5Hyp`**: for every `τ > 0`, eventually in `N`, all entries of the
edge matrices `Θ_{t m(s)²}` (`s = ±`) are at most `N^τ c_κ⁻¹ e^{-c √c_κ |x-y|_L}`. -/
private theorem prop5_edge {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hP : Prop5Hyp κ c) {τ : ℝ}
    (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p : Par κ N) (s : Bool) (x y : Z2 p.L),
      ‖Theta p.L ((p.t : ℂ) * (mSig p.E s * mSig p.E s)) x y‖ ≤
        (N : ℝ) ^ τ * ((gapK κ)⁻¹ *
          Real.exp (-(c * Real.sqrt (gapK κ) * (zdist2 p.L (x - y) : ℝ)))) := by
  filter_upwards [hP τ hτ] with N hN p s x y
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg p.E, p.hE]
  have hg := gapK_pos hκ hκ2
  have hgξ := gap_le_norm_mSig hκ p.hE p.ht0 s
  have h := hN ⟨p, if s then 0 else 1, x, y⟩
  have hξ : xiSet p.E p.t (if s then 0 else 1) = (p.t : ℂ) * mSig p.E s ^ 2 := by
    cases s <;> simp [xiSet]
  simp only [hξ] at h
  rw [← sq] at *
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) τ)
  exact edge_rhs_le hg (gapK_le_one κ) hgξ hc (Nat.cast_nonneg _) p.hL

end Gap

/-! ## 6. Assembly: the deterministic bounds and the absorption of `N^τ` -/

section Assembly

private theorem norm_one_apply_le' {L : ℕ} [NeZero L] (κ : ℝ) (x y : Z2 L) :
    ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x y‖ ≤ Real.exp (-(κ * (zdist2 L (x - y) : ℝ))) := by
  by_cases h : x = y
  · subst h; simp
  · rw [Matrix.one_apply_ne h, norm_zero]; exact (Real.exp_pos _).le

private theorem exists_pair {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (a : Fin n → Z2 L) :
    ∃ i j : Fin n, maxDist L a = zdist2 L (a i - a j) := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n × Fin n))
    Finset.univ_nonempty fun p : Fin n × Fin n => zdist2 L (a p.1 - a p.2)
  exact ⟨p.1, p.2, hp⟩

/-- **The absorption of `N^τ`**: `B = N^{τ/(2m)} G + 1`, `m ≥ 1`, and a constant `C`. -/
private theorem absorb (m : ℕ) (hm : 0 < m) (G C : ℝ) (hG : 0 ≤ G) (hC : 0 ≤ C) {τ : ℝ}
    (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, 1 ≤ (N : ℝ) ∧
      C * ((N : ℝ) ^ (τ / (2 * (m : ℝ))) * G + 1) ^ m ≤ (N : ℝ) ^ τ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  filter_upwards [Filter.eventually_ge_atTop 1,
    eventually_le_rpow (C * (G + 1) ^ m) (half_pos hτ)] with N hN1 hNC
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  refine ⟨hN1', ?_⟩
  have hp : 1 ≤ (N : ℝ) ^ (τ / (2 * (m : ℝ))) := Real.one_le_rpow hN1' (by positivity)
  have h1 : (N : ℝ) ^ (τ / (2 * (m : ℝ))) * G + 1 ≤ (N : ℝ) ^ (τ / (2 * (m : ℝ))) * (G + 1) := by
    nlinarith
  have h2 : ((N : ℝ) ^ (τ / (2 * (m : ℝ))) * G + 1) ^ m
      ≤ ((N : ℝ) ^ (τ / (2 * (m : ℝ))) * (G + 1)) ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  have h3 : ((N : ℝ) ^ (τ / (2 * (m : ℝ)))) ^ m = (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    field_simp
  calc C * ((N : ℝ) ^ (τ / (2 * (m : ℝ))) * G + 1) ^ m
      ≤ C * (((N : ℝ) ^ (τ / (2 * (m : ℝ)))) ^ m * (G + 1) ^ m) := by
        rw [← mul_pow]
        exact mul_le_mul_of_nonneg_left h2 hC
    _ = (N : ℝ) ^ (τ / 2) * (C * (G + 1) ^ m) := by rw [h3]; ring
    _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) :=
        mul_le_mul_of_nonneg_left hNC (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = (N : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half N hτ

/-- The edge entries with the constant `B = N^{τ'} c_κ⁻¹ + 1`: `Θ`, `Θ - 1` and `1`. -/
private theorem prop5_entries {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hP : Prop5Hyp κ c)
    {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p : Par κ N) (s : Bool) (x y : Z2 p.L),
      ‖thetaEdge p.L (mSig p.E) p.t s s x y‖ ≤
        ((N : ℝ) ^ τ' * (gapK κ)⁻¹ + 1) *
          Real.exp (-(c * Real.sqrt (gapK κ) * (zdist2 p.L (x - y) : ℝ))) ∧
      ‖(thetaEdge p.L (mSig p.E) p.t s s - 1) x y‖ ≤
        ((N : ℝ) ^ τ' * (gapK κ)⁻¹ + 1) *
          Real.exp (-(c * Real.sqrt (gapK κ) * (zdist2 p.L (x - y) : ℝ))) := by
  filter_upwards [prop5_edge hκ hc hP hτ'] with N hN p s x y
  have h := hN p s x y
  have h1 := norm_one_apply_le' (L := p.L) (c * Real.sqrt (gapK κ)) x y
  set e := Real.exp (-(c * Real.sqrt (gapK κ) * (zdist2 p.L (x - y) : ℝ))) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hA : 0 ≤ (N : ℝ) ^ τ' * (gapK κ)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (inv_nonneg.2 (gapK_nonneg κ))
  have hT : ‖thetaEdge p.L (mSig p.E) p.t s s x y‖ ≤ (N : ℝ) ^ τ' * (gapK κ)⁻¹ * e := by
    calc _ ≤ _ := h
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · nlinarith
  · rw [Matrix.sub_apply]
    have h2 := norm_sub_le (thetaEdge p.L (mSig p.E) p.t s s x y)
      ((1 : Matrix (Z2 p.L) (Z2 p.L) ℂ) x y)
    have h1' : ‖(1 : Matrix (Z2 p.L) (Z2 p.L) ℂ) x y‖ ≤ e := by
      simpa [he, mul_assoc] using h1
    nlinarith

end Assembly

section Deterministic

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- **Deterministic core of the short-range bound**. -/
private theorem SigmaPi_bound {E t : ℝ} (hn : 3 ≤ n) (σ : Fin n → Bool) (d : Fin n → Z2 L)
    {B κe : ℝ} (hB : 1 ≤ B) (hκe : 0 < κe)
    (hE' : ∀ s : Bool, ∀ x y, ‖(thetaEdge L (mSig E) t s s - 1) x y‖ ≤
      B * Real.exp (-(κe * (zdist2 L (x - y) : ℝ)))) :
    ‖SigmaPi L (mSig E) t σ ∅ d‖ ≤
      ((TSP n).card : ℝ) *
        (B ^ (n + n * n) * (((1 + 2 / (κe / (2 * ((n * n : ℕ) : ℝ)))) ^ 2) ^ (n * n))) *
        Real.exp (-(κe / 2 * (maxDist L d : ℝ))) := by
  obtain ⟨i, j, hij⟩ := exists_pair d
  set X := B ^ (n + n * n) * (((1 + 2 / (κe / (2 * ((n * n : ℕ) : ℝ)))) ^ 2) ^ (n * n)) *
    Real.exp (-(κe / 2 * (maxDist L d : ℝ))) with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ B := by linarith
    have hnn : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
      have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
    have : 0 ≤ (1 + 2 / (κe / (2 * ((n * n : ℕ) : ℝ)))) := by positivity
    positivity
  have hone : ∀ x y, ‖(1 : Matrix (Z2 L) (Z2 L) ℂ) x y‖ ≤
      B * Real.exp (-(κe * (zdist2 L (x - y) : ℝ))) := fun x y =>
    (norm_one_apply_le' κe x y).trans
      (le_mul_of_one_le_left (Real.exp_pos _).le hB)
  have htree : ∀ F ∈ TSPlong n σ ∅, ‖selfE L (mSig E) t σ F d‖ ≤ X := by
    intro F hF
    have hFT := (mem_filter.1 hF).1
    have hFl : Flong F σ = ∅ := (mem_filter.1 hF).2
    have hsame : ∀ e ∈ F, σ e.1 = σ e.2 := by
      intro e he
      by_contra h
      have : e ∈ Flong F σ := mem_filter.2 ⟨he, h⟩
      rw [hFl] at this
      simp at this
    have hself : selfE L (mSig E) t σ F d = treeValW L F d (fun _ => 1)
        (fun e => thetaEdge L (mSig E) t (σ e.1.1) (σ e.1.2) - 1) := by
      simp only [selfE, selfW, treeValW, Matrix.one_apply]
    rw [hself, hX, hij]
    refine tree_bound (isTSPf_of_mem hFT) (by omega) d _ _ hB hκe
      (fun v x y => hone x y) (fun e x y => ?_) i j
    have := hsame e.1 e.2
    simp only [← this]
    exact hE' _ x y
  have hsum : ‖SigmaPi L (mSig E) t σ ∅ d‖ ≤ (TSPlong n σ ∅).card * X := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum htree).trans ?_
    rw [sum_const, nsmul_eq_mul]
  have hcard : ((TSPlong n σ ∅).card : ℝ) ≤ (TSP n).card := by
    exact_mod_cast card_le_card (filter_subset _ _)
  calc _ ≤ (TSPlong n σ ∅).card * X := hsum
    _ ≤ (TSP n).card * X := mul_le_mul_of_nonneg_right hcard hX0
    _ = _ := by rw [hX]; ring

end Deterministic

/-! ## 7. The theorems -/

section Statements

/-- **`(res_SIGempdd)` in `≺` form**: for `n ≥ 3` and every sign
vector `σ`, `‖Σ^{(∅)}(t, σ, d)‖ ≺ e^{-(c √c_κ / 2) max_{ij} |d_i - d_j|_L}`.  Conditional on
`Prop5Hyp κ c` (property 5 of `lem_propTH`). -/
theorem SigmaPi_empty_shortRange_prec :
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c →
    UnifDetDom (U := fun N => (p : Par κ N) × (Fin n → Bool) × (Fin n → Z2 p.L))
      (fun _ u => ‖SigmaPi u.1.L (mSig u.1.E) u.1.t u.2.1 ∅ u.2.2‖)
      (fun _ u => Real.exp (-(c * Real.sqrt (gapK κ) / 2 * (maxDist u.1.L u.2.2 : ℝ)))) := by
  intro n _ hn κ c hκ hc hP τ hτ
  by_cases hκ2 : κ ≤ 2
  swap
  · refine Filter.Eventually.of_forall fun N u => ?_
    exfalso
    have h1 := u.1.hE
    have h2 := abs_nonneg u.1.E
    have h3 := not_le.1 hκ2
    linarith
  have hg := gapK_pos hκ hκ2
  have hm : 0 < n + n * n := by have := NeZero.pos n; positivity
  have hm' : (0 : ℝ) < ((n + n * n : ℕ) : ℝ) := by exact_mod_cast hm
  have hτ' : 0 < τ / (2 * ((n + n * n : ℕ) : ℝ)) := by positivity
  have hκe : 0 < c * Real.sqrt (gapK κ) := mul_pos hc (Real.sqrt_pos.2 hg)
  have hnn : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
    have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
  have hC : 0 ≤ ((TSP n).card : ℝ) *
      (((1 + 2 / (c * Real.sqrt (gapK κ) / (2 * ((n * n : ℕ) : ℝ)))) ^ 2) ^ (n * n)) := by
    have : 0 ≤ (1 + 2 / (c * Real.sqrt (gapK κ) / (2 * ((n * n : ℕ) : ℝ)))) := by positivity
    positivity
  filter_upwards [absorb (n + n * n) hm (gapK κ)⁻¹ _ (inv_nonneg.2 hg.le) hC hτ,
    prop5_entries hκ hc hP hτ'] with N habs hent u
  obtain ⟨hN1, habs⟩ := habs
  rcases u with ⟨p, σ, d⟩
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hA : 0 ≤ (N : ℝ) ^ (τ / (2 * ((n + n * n : ℕ) : ℝ))) * (gapK κ)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (inv_nonneg.2 hg.le)
  have h := SigmaPi_bound (E := p.E) (t := p.t) hn σ d
    (B := (N : ℝ) ^ (τ / (2 * ((n + n * n : ℕ) : ℝ))) * (gapK κ)⁻¹ + 1) (by linarith) hκe
    (fun s x y => (hent p s x y).2)
  refine h.trans ?_
  calc _ = (((TSP n).card : ℝ) *
        (((1 + 2 / (c * Real.sqrt (gapK κ) / (2 * ((n * n : ℕ) : ℝ)))) ^ 2) ^ (n * n)) *
      (((N : ℝ) ^ (τ / (2 * ((n + n * n : ℕ) : ℝ))) * (gapK κ)⁻¹ + 1) ^ (n + n * n))) *
        Real.exp (-(c * Real.sqrt (gapK κ) / 2 * (maxDist p.L d : ℝ))) := by ring
    _ ≤ (N : ℝ) ^ τ * Real.exp (-(c * Real.sqrt (gapK κ) / 2 * (maxDist p.L d : ℝ))) :=
        mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le

end Statements

end RBM.KLoop
