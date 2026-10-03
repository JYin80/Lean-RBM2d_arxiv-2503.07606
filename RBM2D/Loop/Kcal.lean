/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Propagator.Deriv
import RBM2D.Propagator.Bounds
import RBM2D.Propagator.Elliptic
import RBM2D.Hierarchy.OperationsPair
import RBM2D.Gauss.SpectralWindow
import RBM2D.Gauss.SpectralAlgebra
import RBM2D.Defs.Domination
import RBM2D.Defs.Dist

/-!
# The primitive loops `𝒦` (tree representation) and the definitions of Section 3

`𝒦_{t,σ,a}` is defined by the explicit tree sum of [YY_25] Lemma 3.4, (3.5), in `d = 2`:
`Kcal = Kgen (mSig E)`; `n = 1`: `m(σ₁)`; `n = 2`: `(Kn2sol)`; `n ≥ 3`:
`m_σ W^{-2(n-1)} ∑_{F ∈ TSP n} Γ_F`.  The construction parallels the one-dimensional
formalization, with `ZMod L ↦ Z2 L` and `W⁻¹ ↦ (W²)⁻¹` per edge.

Public: the definitions and the theorems `WI_calK_two`, `Kcal_two`, `Kcal_two_cases`,
`Kcal_eq_sum_Kpi`, `Kpi_eq_sum_SigmaPi`, `SigmaPi_empty_symm`.
-/

namespace RBM.KLoop

open Finset

/-! ## 1. The polygon: diagonals and crossing-free sets ([YY_25] Def 3.1, Lemma 3.2) -/

/-- `{i, j}` (`i < j`) is a diagonal of the `n`-gon: the vertices are not adjacent modulo
`n`.  The definition is dimension-free. -/
def IsDiag (n : ℕ) (i j : Fin n) : Prop :=
  i < j ∧ j.val ≠ i.val + 1 ∧ ¬(i.val = 0 ∧ j.val = n - 1)

instance (n : ℕ) (i j : Fin n) : Decidable (IsDiag n i j) := by
  unfold IsDiag; infer_instance

/-- The diagonals of the `n`-gon, as ordered pairs `(i, j)` with `i < j`. -/
def diagonals (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => IsDiag n p.1 p.2

/-- The crossing condition of [YY_25] Lemma 3.2. -/
def Crossing {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2) ∨ (f.1 < e.1 ∧ e.1 < f.2 ∧ f.2 < e.2)

instance {n : ℕ} (e f : Fin n × Fin n) : Decidable (Crossing e f) := by
  unfold Crossing; infer_instance

/-- No two pairs of `F` cross. -/
def CrossingFree {n : ℕ} (F : Finset (Fin n × Fin n)) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, ¬Crossing e f

instance {n : ℕ} (F : Finset (Fin n × Fin n)) : Decidable (CrossingFree F) := by
  unfold CrossingFree; infer_instance

/-- `T_SP(P_a)` of [YY_25] Definition 3.3, via [YY_25] Lemma 3.2: the crossing-free sets of
diagonals of the `n`-gon. -/
def TSP (n : ℕ) : Finset (Finset (Fin n × Fin n)) :=
  (diagonals n).powerset.filter CrossingFree

/-! ## 2. The tree of a crossing-free set ([YY_25] Definition 3.3) -/

section Laminar

variable {n : ℕ} [NeZero n]

/-- The root node `(0, n - 1)`, whose arc contains every non-root vertex. -/
def wholeP (n : ℕ) [NeZero n] : Fin n × Fin n :=
  (0, ⟨n - 1, by have := NeZero.pos n; omega⟩)

/-- Vertex `v` lies in the arc of `d = (i, j)`: `i ≤ v < j`. -/
def InArc (d : Fin n × Fin n) (v : Fin n) : Prop := d.1 ≤ v ∧ v < d.2

instance (d : Fin n × Fin n) (v : Fin n) : Decidable (InArc d v) := by
  unfold InArc; infer_instance

/-- The arc of `d` is contained in the arc of `e`. -/
def ArcLe (d e : Fin n × Fin n) : Prop := e.1 ≤ d.1 ∧ d.2 ≤ e.2

instance (d e : Fin n × Fin n) : Decidable (ArcLe d e) := by
  unfold ArcLe; infer_instance

/-- The width `j - i` of the arc of `(i, j)`. -/
def arcWidth (d : Fin n × Fin n) : ℕ := d.2.val - d.1.val

/-- The internal vertices of the tree of `F`: `F ∪ {whole}`. -/
def nodes (F : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) := insert (wholeP n) F

theorem wholeP_mem_nodes (F : Finset (Fin n × Fin n)) : wholeP n ∈ nodes F :=
  mem_insert_self _ _

theorem mem_nodes_of_mem {F : Finset (Fin n × Fin n)} {d : Fin n × Fin n} (h : d ∈ F) :
    d ∈ nodes F := mem_insert_of_mem h

/-- The smallest node of a set of candidates, or `whole` if there is none. -/
noncomputable def minNode (s : Finset (Fin n × Fin n)) : Fin n × Fin n :=
  if h : s.Nonempty then Classical.choose (s.exists_min_image arcWidth h) else wholeP n

theorem minNode_mem_or {s : Finset (Fin n × Fin n)} :
    minNode s ∈ s ∨ minNode s = wholeP n := by
  unfold minNode
  split_ifs with h
  · exact Or.inl (Classical.choose_spec (s.exists_min_image arcWidth h)).1
  · exact Or.inr rfl

/-- The parent of the leaf `v`: the smallest node whose arc contains `v`. -/
noncomputable def leafPar (F : Finset (Fin n × Fin n)) (v : Fin n) : Fin n × Fin n :=
  minNode ((nodes F).filter fun e => InArc e v)

/-- The parent of the node `d`: the smallest other node whose arc contains the arc of `d`. -/
noncomputable def nodePar (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n) : Fin n × Fin n :=
  minNode ((nodes F).filter fun e => ArcLe d e ∧ e ≠ d)

theorem leafPar_mem (F : Finset (Fin n × Fin n)) (v : Fin n) : leafPar F v ∈ nodes F := by
  rcases minNode_mem_or (s := (nodes F).filter fun e => InArc e v) with h | h
  · exact (mem_filter.1 h).1
  · rw [leafPar, h]; exact wholeP_mem_nodes F

theorem nodePar_mem (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n) :
    nodePar F d ∈ nodes F := by
  rcases minNode_mem_or (s := (nodes F).filter fun e => ArcLe d e ∧ e ≠ d) with h | h
  · exact (mem_filter.1 h).1
  · rw [nodePar, h]; exact wholeP_mem_nodes F

/-- Over the empty family every leaf hangs on `whole`: the star. -/
theorem leafPar_empty (v : Fin n) : leafPar (∅ : Finset (Fin n × Fin n)) v = wholeP n := by
  rcases minNode_mem_or (s := (nodes (∅ : Finset (Fin n × Fin n))).filter fun e => InArc e v)
    with h | h
  · have h1 := (mem_filter.1 h).1
    have h2 : (nodes (∅ : Finset (Fin n × Fin n))) = {wholeP n} := by simp [nodes]
    rw [h2, mem_singleton] at h1
    exact h1
  · exact h

end Laminar

/-! ## 3. The definition of `𝒦` -/

section Value

variable (L : ℕ) [NeZero L]

/-- `m(σ)` of `(def_mtzk)`: `m^{(E)}` for `+` (`true`), its conjugate
for `−` (`false`). -/
noncomputable def mSig (E : ℝ) (s : Bool) : ℂ :=
  if s then Gauss.spectralM E else (starRingEnd ℂ) (Gauss.spectralM E)

/-- The edge weight `Θ^{(B)}_{t m(s) m(s')}`. -/
noncomputable def thetaEdge (m : Bool → ℂ) (t : ℝ) (s s' : Bool) : Matrix (Z2 L) (Z2 L) ℂ :=
  Theta L ((t : ℂ) * (m s * m s'))

/-- The value of the tree of `F` with leaf weights `M v` and internal edge weights `E d`:
`∑_b ∏_v (M_v)_{a_v, b(par v)} ∏_{d ∈ F} (E_d)_{b(d), b(par d)}`, summed over the labels
`b` of all internal vertices. -/
noncomputable def treeValW {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n)) (a : Fin n → Z2 L)
    (M : Fin n → Matrix (Z2 L) (Z2 L) ℂ) (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) : ℂ :=
  ∑ b : ↥(nodes F) → Z2 L,
    (∏ v : Fin n, M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)) *
      ∏ d : ↥F, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)

/-- [YY_25] Definition 3.3: `Γ_F(t, σ, a)`, leaf edges `Θ_{t m_v m_{v+1}}`, internal edges
`Θ_{t m_i m_j} - 1`. -/
noncomputable def treeValG {n : ℕ} [NeZero n] (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → Z2 L) (F : Finset (Fin n × Fin n)) : ℂ :=
  treeValW L F a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
    (fun d => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1)

/-- [YY_25] (3.5) in `d = 2`: `m_σ W^{-2(n-1)} ∑_{F ∈ T_SP(n)} Γ_F`. -/
noncomputable def Kn (W : ℕ) (m : Bool → ℂ) (t : ℝ) (n : ℕ) [NeZero n] (σ : Fin n → Bool)
    (a : Fin n → Z2 L) : ℂ :=
  (∏ i, m (σ i)) * ((W : ℂ) ^ 2)⁻¹ ^ (n - 1) * ∑ F ∈ TSP n, treeValG L m t σ a F

/-- `(Kn2sol)`: `W⁻² m₁ m₂ (Θ_{t m₁ m₂})_{a₁ a₂}`. -/
noncomputable def kTwo (W : ℕ) (m : Bool → ℂ) (t : ℝ) (s₁ s₂ : Bool) (a₁ a₂ : Z2 L) : ℂ :=
  ((W : ℂ) ^ 2)⁻¹ * (m s₁ * m s₂) * Theta L ((t : ℂ) * (m s₁ * m s₂)) a₁ a₂

/-- The tree representation on loop indices, for a general `m : Bool → ℂ`: `m(σ₁)` for
`n = 1`, `(Kn2sol)` for `n = 2`, `Kn` for `n ≥ 3`; `0` on the empty loop. -/
noncomputable def Kgen (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (Z2 L)) : ℂ :=
  if I.length = 1 then m (I.σ.getD 0 false)
  else if I.length = 2 then
    kTwo L W m t (I.σ.getD 0 false) (I.σ.getD 1 false) (I.a.getD 0 0) (I.a.getD 1 0)
  else if h : 3 ≤ I.length then
    haveI : NeZero I.length := ⟨by omega⟩
    Kn L W m t I.length (fun i => I.σ.getD i false) (fun i => I.a.getD i 0)
  else 0

/-- **The primitive loop** `𝒦_{t,σ,a}` of `Def_Ktza`, at energy `E`. -/
noncomputable def Kcal (W : ℕ) (E t : ℝ) (I : LoopIdx (Z2 L)) : ℂ :=
  Kgen L W (mSig E) t I

/-- The loop index of a sign vector and a label vector of the same length `n`. -/
def loopOf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Z2 L) : LoopIdx (Z2 L) :=
  ⟨List.ofFn σ, List.ofFn a⟩

end Value

/-! ## 4. The equation `(pro_dyncalK)` as a predicate -/

section Primitive

variable (L : ℕ) [NeZero L]

/-- The right-hand side of `(pro_dyncalK)`, with `(calGonIND)`:
`W² ∑_{1≤k<l≤n} ∑_{a,b} K(𝒢^{(a),L}_{k,l}(σ,a)) S^{(B)}_{ab} K(𝒢^{(b),R}_{k,l}(σ,a))`. -/
noncomputable def primRhs (W : ℕ) (K : LoopIdx (Z2 L) → ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  (W : ℂ) ^ 2 * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Z2 L, ∑ b : Z2 L,
    K (I.cutGlueL k l a) * SB L a b * K (I.cutGlueR k l b)

/-- The initial data of `Def_Ktza`:
`W^{-2(n-1)} ∏_k m(σ_k) 1(a₁ = ⋯ = aₙ)`. -/
noncomputable def primInit (W : ℕ) (m : Bool → ℂ) (I : LoopIdx (Z2 L)) : ℂ :=
  ((W : ℂ) ^ 2)⁻¹ ^ (I.length - 1) * (I.σ.map m).prod *
    (if ∀ x ∈ I.a, ∀ y ∈ I.a, x = y then 1 else 0)

/-- `Def_Ktza` as a predicate on a family `K : ℝ → LoopIdx (Z2 L) → ℂ`: `(pro_dyncalK)` at
the times `T` for loops of length `≥ 2`, the initial data at `t = 0`, and `K = m(σ₁)` for
loops of length `1`. -/
def IsPrimitive (W : ℕ) (m : Bool → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (Z2 L) → ℂ) : Prop :=
  (∀ t ∈ T, ∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length →
      HasDerivAt (fun s => K s I) (primRhs L W (K t) I) t) ∧
  (∀ I : LoopIdx (Z2 L), I.WF → 2 ≤ I.length → K 0 I = primInit L W m I) ∧
  (∀ t ∈ T, ∀ (s : Bool) (a : Z2 L), K t ⟨[s], [a]⟩ = m s)

end Primitive

/-! ## 5. Long edges, `K^{(π)}` and `Σ^{(π)}` ([YY_25] Definitions 3.8, 3.9) -/

section Layers

variable {n : ℕ}

/-- [YY_25] Definition 3.8: the long internal edges of `F`, joining vertices of opposite sign. -/
def Flong (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) : Finset (Fin n × Fin n) :=
  F.filter fun d => σ d.1 ≠ σ d.2

/-- [YY_25] Definition 3.8: `T_SP(P_a, σ, π)`, the trees whose long internal edges are exactly
`π`. -/
def TSPlong (n : ℕ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) :=
  (TSP n).filter fun F => Flong F σ = π

private theorem sum_TSPlong {M : Type*} [AddCommMonoid M] (σ : Fin n → Bool)
    (f : Finset (Fin n × Fin n) → M) :
    ∑ π ∈ (diagonals n).powerset, ∑ F ∈ TSPlong n σ π, f F = ∑ F ∈ TSP n, f F := by
  refine sum_fiberwise_of_maps_to (fun F hF => ?_) f
  rw [mem_powerset]
  have hF' := (mem_filter.1 hF).1
  exact (filter_subset _ _).trans (mem_powerset.1 hF')

variable (L : ℕ) [NeZero L] [NeZero n]

/-- [YY_25] (3.40): `K^{(π)}_{t,σ,a}`, the sum of the trees whose long edges are `π`
(`W`-free).  The RBM2D paper uses it in `(KKpi)`. -/
noncomputable def Kpi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Z2 L)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  ∑ F ∈ TSPlong n σ π, treeValG L m t σ a F

/-- The self-energy of one tree: the boundary (leaf) edges are removed, `d_v` is the
internal endpoint of the leaf edge at `a_v`, and all internal vertices are summed. -/
noncomputable def selfW (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ)
    (d : Fin n → Z2 L) : ℂ :=
  ∑ b : ↥(nodes F) → Z2 L,
    (∏ v : Fin n, if d v = b ⟨leafPar F v, leafPar_mem F v⟩ then (1 : ℂ) else 0) *
      ∏ e : ↥F, E e (b ⟨e.1, mem_nodes_of_mem e.2⟩) (b ⟨nodePar F e, nodePar_mem F e⟩)

/-- The self-energy of one tree with internal edges `Θ_{t m_i m_j} - 1`. -/
noncomputable def selfE (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (F : Finset (Fin n × Fin n))
    (d : Fin n → Z2 L) : ℂ :=
  selfW L F (fun e => thetaEdge L m t (σ e.1.1) (σ e.1.2) - 1) d

/-- [YY_25] (3.42): the self-energy `Σ^{(π)}(t, σ, d)`; `Σ^{(∅)}` is the object of
`(SZjadljsk)`, `(res_SIGempdd)` and of the symmetry `g(s) = g(-s)`. -/
noncomputable def SigmaPi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (d : Fin n → Z2 L) : ℂ :=
  ∑ F ∈ TSPlong n σ π, selfE L m t σ F d

end Layers

/-! ## 6. Scales, the parameter set of `≺`, and properties 5–6 as hypotheses -/

section Scales

/-- `η_t = Im z_t = (1 - t) Im m^{(E)}` (`ML:GLoop`). -/
noncomputable def etaT (E t : ℝ) : ℝ := (Gauss.spectralZ E t).im

/-- `ℓ_t = ℓ̂(t) = min(|1 - t|^{-1/2}, L)` (`(eq:bcal_k)`). -/
noncomputable def ellT (L : ℕ) [NeZero L] (t : ℝ) : ℝ := ellhat L (t : ℂ)

/-- `M_t = W² ℓ_t² η_t` (`(eq:bcal_k)`). -/
noncomputable def Mt (L W : ℕ) [NeZero L] (E t : ℝ) : ℝ :=
  (W : ℝ) ^ 2 * ellT L t ^ 2 * etaT E t

/-- The bulk gap `c_κ`: `c_κ ≤ |1 - t m^{(E)2}|` for `t ∈ [0,1]`, `|E| ≤ 2 - κ`. -/
noncomputable def gapK (κ : ℝ) : ℝ := min 1 (Real.sqrt (κ * (4 - κ) / 2))

/-- `max_{i,j} |a_i - a_j|_L`. -/
def maxDist (L : ℕ) [NeZero L] {n : ℕ} (a : Fin n → Z2 L) : ℕ :=
  Finset.univ.sup fun p : Fin n × Fin n => zdist2 L (a p.1 - a p.2)

/-- The parameter set of `≺` at size `N`: `W² L² = N` (Section 1, setting), `L ≥ 3`, `W ≥ 1`,
`|E| ≤ 2 - κ`, `0 ≤ t < 1`. -/
structure Par (κ : ℝ) (N : ℕ) where
  L : ℕ
  W : ℕ
  hL : 3 ≤ L
  hW : 1 ≤ W
  hN : W ^ 2 * L ^ 2 = N
  E : ℝ
  hE : |E| ≤ 2 - κ
  t : ℝ
  ht0 : 0 ≤ t
  ht1 : t < 1

instance Par.neZeroL {κ : ℝ} {N : ℕ} (p : Par κ N) : NeZero p.L := ⟨by have := p.hL; omega⟩

/-- The three spectral parameters `t m², t m̄², t` of properties 5–6 of `lem_propTH`. -/
noncomputable def xiSet (E t : ℝ) (j : Fin 3) : ℂ :=
  ![(t : ℂ) * mSig E true ^ 2, (t : ℂ) * mSig E false ^ 2, (t : ℂ)] j

/-- **Property 5 of `lem_propTH`, `(prop:ThfadC)`, as a hypothesis**, with
the decay constant `c` of the paper as a parameter:
`(Θ_ξ)_{ab} ≺ e^{-c |a-b|_L / ℓ̂(ξ)} / (|1-ξ| ℓ̂(ξ)²)` for `ξ ∈ {t m², t m̄², t}`. -/
def Prop5Hyp (κ c : ℝ) : Prop :=
  UnifDetDom (U := fun N => (p : Par κ N) × Fin 3 × Z2 p.L × Z2 p.L)
    (fun _ u => ‖Theta u.1.L (xiSet u.1.E u.1.t u.2.1) u.2.2.1 u.2.2.2‖)
    (fun _ u =>
      Real.exp (-(c * (zdist2 u.1.L (u.2.2.1 - u.2.2.2) : ℝ)) /
          ellhat u.1.L (xiSet u.1.E u.1.t u.2.1)) /
        (‖(1 : ℂ) - xiSet u.1.E u.1.t u.2.1‖ * ellhat u.1.L (xiSet u.1.E u.1.t u.2.1) ^ 2))

/-- **Property 6 of `lem_propTH`, `(prop:BD1)` and `(prop:BD2)`, as a hypothesis**, for
`ξ ∈ {t m², t m̄², t}` and every shift `s`. -/
def Prop6Hyp (κ : ℝ) : Prop :=
  UnifDetDom (U := fun N => (p : Par κ N) × Fin 3 × Z2 p.L × Z2 p.L × Z2 p.L)
    (fun _ u =>
      ‖Theta u.1.L (xiSet u.1.E u.1.t u.2.1) u.2.2.1 u.2.2.2.1
        - Theta u.1.L (xiSet u.1.E u.1.t u.2.1) u.2.2.1 (u.2.2.2.1 + u.2.2.2.2)‖)
    (fun _ u =>
      (zdist2 u.1.L u.2.2.2.2 : ℝ) / ((zdist2 u.1.L (u.2.2.1 - u.2.2.2.1) : ℝ) + 1)
        + (zdist2 u.1.L u.2.2.2.2 : ℝ) /
          (ellhat u.1.L (xiSet u.1.E u.1.t u.2.1) ^ 2 *
            Real.sqrt ‖(1 : ℂ) - xiSet u.1.E u.1.t u.2.1‖)) ∧
  UnifDetDom (U := fun N => (p : Par κ N) × Fin 3 × Z2 p.L × Z2 p.L × Z2 p.L)
    (fun _ u =>
      ‖2 * Theta u.1.L (xiSet u.1.E u.1.t u.2.1) u.2.2.1 u.2.2.2.1
        - Theta u.1.L (xiSet u.1.E u.1.t u.2.1) u.2.2.1 (u.2.2.2.1 + u.2.2.2.2)
        - Theta u.1.L (xiSet u.1.E u.1.t u.2.1) u.2.2.1 (u.2.2.2.1 - u.2.2.2.2)‖)
    (fun _ u =>
      (zdist2 u.1.L u.2.2.2.2 : ℝ) ^ 2 / ((zdist2 u.1.L (u.2.2.1 - u.2.2.2.1) : ℝ) ^ 2 + 1)
        + (zdist2 u.1.L u.2.2.2.2 : ℝ) ^ 2 / ellhat u.1.L (xiSet u.1.E u.1.t u.2.1) ^ 2)

end Scales
/-- The alternating sign vector `σ^{(alt)}` of `(assum_SZ_SinMole)` (0-based: `+` at even
positions). -/
def sigAlt (n : ℕ) : Fin n → Bool := fun k => decide (k.val % 2 = 0)

/-! ## 7. Proved facts -/

section Proofs

variable (L : ℕ) [NeZero L]

/-- [YY_25] (3.41) at the level of the tree sum. -/
private theorem Kn_eq_sum_Kpi (W : ℕ) (m : Bool → ℂ) (t : ℝ) {n : ℕ} [NeZero n] (σ : Fin n → Bool)
    (a : Fin n → Z2 L) :
    Kn L W m t n σ a =
      (∏ i, m (σ i)) * ((W : ℂ) ^ 2)⁻¹ ^ (n - 1) *
        ∑ π ∈ (diagonals n).powerset, Kpi L m t σ a π := by
  simp only [Kn, Kpi]
  rw [sum_TSPlong]

/-- Transport of `Kn` along an equality of lengths. -/
private theorem Kn_cast (W : ℕ) (m : Bool → ℂ) (t : ℝ) {k k' : ℕ} (hk : NeZero k) (hk' : NeZero k')
    (h : k = k')
    (σ : Fin k → Bool) (a : Fin k → Z2 L) (σ' : Fin k' → Bool) (a' : Fin k' → Z2 L)
    (hσ : ∀ i : Fin k, σ i = σ' (Fin.cast h i)) (ha : ∀ i : Fin k, a i = a' (Fin.cast h i)) :
    @Kn L _ W m t k hk σ a = @Kn L _ W m t k' hk' σ' a' := by
  subst h
  have h1 : σ = σ' := funext fun i => by simpa using hσ i
  have h2 : a = a' := funext fun i => by simpa using ha i
  subst h1 h2
  rfl

/-- On `loopOf σ a` with `n ≥ 3`, the loop-index form `Kgen` is the tree sum `Kn`. -/
private theorem Kgen_loopOf (W : ℕ) (m : Bool → ℂ) (t : ℝ) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (σ : Fin n → Bool) (a : Fin n → Z2 L) :
    Kgen L W m t (loopOf L σ a) = Kn L W m t n σ a := by
  have hlen : (loopOf L σ a).length = n := by simp [loopOf, LoopIdx.length]
  have h1 : (loopOf L σ a).length ≠ 1 := by omega
  have h2 : (loopOf L σ a).length ≠ 2 := by omega
  have h3 : 3 ≤ (loopOf L σ a).length := by omega
  simp only [Kgen, h1, h2, ↓reduceIte, h3, ↓reduceDIte]
  refine Kn_cast L W m t _ _ hlen _ _ _ _ (fun i => ?_) (fun i => ?_)
  · have hi : (i : ℕ) < n := by have := i.isLt; omega
    simp [loopOf, List.getD_eq_getElem?_getD, hi]
    rfl
  · have hi : (i : ℕ) < n := by have := i.isLt; omega
    simp [loopOf, List.getD_eq_getElem?_getD, hi]
    rfl

/-- Re-attaching the leaf edges to the self-energy gives back the tree value. -/
private theorem treeValW_eq_sum_selfW {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n))
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

private theorem norm_mSig {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : ‖mSig E s‖ = 1 := by
  cases s <;> simp [mSig, Gauss.norm_spectralM hE]

/-- `‖t m(s) m(s')‖ = t` for `t ≥ 0`. -/
private theorem norm_xi {E t : ℝ} (hE : |E| ≤ 2) (ht : 0 ≤ t) (s s' : Bool) :
    ‖(t : ℂ) * (mSig E s * mSig E s')‖ = t := by
  rw [norm_mul, norm_mul, norm_mSig hE, norm_mSig hE, Complex.norm_real,
    Real.norm_of_nonneg ht, mul_one, mul_one]

/-- Reflection invariance of `Θ_ξ`: `(Θ_ξ)_{x-p, x-q} = (Θ_ξ)_{pq}` (properties 1–2). -/
private theorem Theta_reflect (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x p q : Z2 L) :
    Theta L ξ (x - p) (x - q) = Theta L ξ p q := by
  have h1 := Theta_apply_add_right L hL hξ q p (x - p - q)
  have e1 : q + (x - p - q) = x - p := by abel
  have e2 : p + (x - p - q) = x - q := by abel
  rw [e1, e2] at h1
  rw [h1]
  have h2 := congrFun (congrFun (Theta_transpose L hL hξ) p) q
  simpa [Matrix.transpose_apply] using h2

/-- Reflection of the self-energy of one tree. -/
private theorem selfW_reflect {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n))
    (E : ↥F → Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L)
    (hE : ∀ e p q, E e (x - p) (x - q) = E e p q) (d : Fin n → Z2 L) :
    selfW L F E (fun i => x - d i) = selfW L F E d := by
  unfold selfW
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => Equiv.subLeft x) _ _ fun b => ?_
  simp only [Equiv.piCongrRight_apply]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    have hiff : ∀ y : Z2 L, (x - d v = y) ↔ (d v = x - y) := fun y => by
      constructor
      · intro h; rw [← h, sub_sub_cancel]
      · intro h; rw [h, sub_sub_cancel]
    simp only [hiff]
    rfl
  · refine Finset.prod_congr rfl fun e _ => ?_
    exact (hE _ _ _).symm

/-- **`(WI_calK)` at `n = 2`** (the case `σ = (+,-)` of `(WI_calK)`). -/
theorem WI_calK_two (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) (a₁ : Z2 L) :
    ∑ x : Z2 L, Kcal L W E t ⟨true :: [] ++ [false], [a₁] ++ [x]⟩
      = (2 * Complex.I * (W : ℂ) ^ 2 * (etaT E t : ℂ))⁻¹ *
          (Kcal L W E t ⟨true :: [], [a₁]⟩ - Kcal L W E t ⟨false :: [], [a₁]⟩) := by
  have hE2 : |E| ≤ 2 := hE.le
  have hm : mSig E true * mSig E false = 1 := by
    simp only [mSig, ↓reduceIte, Bool.false_eq_true]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Gauss.norm_spectralM hE2]
    simp
  have hξ : ‖(t : ℂ) * (mSig E true * mSig E false)‖ < 1 := by
    rw [norm_xi hE2 ht.1]; exact ht.2
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  have him : 0 < (Gauss.spectralM E).im := Gauss.spectralM_im_pos hE
  have ht1 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
  have hLHS : ∑ x : Z2 L, Kcal L W E t ⟨true :: [] ++ [false], [a₁] ++ [x]⟩
      = ((W : ℂ) ^ 2)⁻¹ * (mSig E true * mSig E false) *
          (1 - (t : ℂ) * (mSig E true * mSig E false))⁻¹ := by
    rw [← sum_Theta_row L hL hξ a₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Kcal, Kgen, kTwo, LoopIdx.length]
  rw [hLHS, hm]
  simp only [Kcal, Kgen, LoopIdx.length, List.length_cons, List.length_nil, zero_add,
    ↓reduceIte, List.getD_cons_zero, mSig, Bool.false_eq_true, Complex.sub_conj]
  rw [etaT, Gauss.spectralZ_im]
  have him0 : ((Gauss.spectralM E).im : ℂ) ≠ 0 := by exact_mod_cast him.ne'
  have ht0 : ((1 : ℂ) - t) ≠ 0 := by exact_mod_cast ht1
  push_cast
  field_simp

end Proofs

/-! ## 8. The theorems -/

section Statements

/-- **`(Kn2sol)`**: for `n = 2`,
`𝒦_{t,σ,(a₁,a₂)} = W⁻² m₁ m₂ (Θ_{t m₁ m₂})_{a₁ a₂}`. -/
theorem Kcal_two :
  ∀ (L W : ℕ) [NeZero L] (E t : ℝ) (s₁ s₂ : Bool) (a₁ a₂ : Z2 L),
    Kcal L W E t ⟨[s₁, s₂], [a₁, a₂]⟩
      = ((W : ℂ) ^ 2)⁻¹ * (mSig E s₁ * mSig E s₂)
          * Theta L ((t : ℂ) * (mSig E s₁ * mSig E s₂)) a₁ a₂ := by
  intro L W _ E t s₁ s₂ a₁ a₂
  simp [Kcal, Kgen, kTwo, LoopIdx.length]

/-- **`(Kn2sol2)`**: the cases `σ = (+,-)` and `σ = (+,+)`. -/
theorem Kcal_two_cases :
  ∀ (L W : ℕ) [NeZero L] (E t : ℝ) (a b : Z2 L),
    Kcal L W E t ⟨[true, false], [a, b]⟩
        = ((W : ℂ) ^ 2)⁻¹ * (Complex.normSq (Gauss.spectralM E) : ℂ)
            * Ring.inverse
                (1 - ((t : ℂ) * (Complex.normSq (Gauss.spectralM E) : ℂ)) • SB L) a b ∧
      Kcal L W E t ⟨[true, true], [a, b]⟩
        = ((W : ℂ) ^ 2)⁻¹ * Gauss.spectralM E ^ 2
            * Ring.inverse (1 - ((t : ℂ) * Gauss.spectralM E ^ 2) • SB L) a b := by
  intro L W _ E t a b
  refine ⟨?_, ?_⟩
  · simp [Kcal, Kgen, kTwo, LoopIdx.length, mSig, Theta, Complex.mul_conj]
  · simp [Kcal, Kgen, kTwo, LoopIdx.length, mSig, Theta, sq]

/-- **`(KKpi)`**, i.e. [YY_25] (3.41), for `n ≥ 3`:
`𝒦_{t,σ,a} = W^{-2(n-1)} m_σ ∑_π K^{(π)}_{t,σ,a}`. -/
theorem Kcal_eq_sum_Kpi :
  ∀ (L W : ℕ) [NeZero L] (E t : ℝ) (n : ℕ) [NeZero n], 3 ≤ n →
    ∀ (σ : Fin n → Bool) (a : Fin n → Z2 L),
      Kcal L W E t (loopOf L σ a)
        = ((W : ℂ) ^ 2)⁻¹ ^ (n - 1) * (∏ i, mSig E (σ i)) *
            ∑ π ∈ (diagonals n).powerset, Kpi L (mSig E) t σ a π := by
  intro L W _ E t n _ hn σ a
  rw [Kcal, Kgen_loopOf L W (mSig E) t hn σ a, Kn_eq_sum_Kpi]
  ring

/-- **The summand display of `(KKpi)`**, [YY_25] (3.42):
`K^{(π)}_{t,σ,a} = ∑_d Σ^{(π)}(t,σ,d) ∏_i (Θ_{t m_i m_{i+1}})_{a_i d_i}`. -/
theorem Kpi_eq_sum_SigmaPi :
  ∀ (L : ℕ) [NeZero L] (E t : ℝ) (n : ℕ) [NeZero n] (σ : Fin n → Bool) (a : Fin n → Z2 L)
    (π : Finset (Fin n × Fin n)),
    Kpi L (mSig E) t σ a π
      = ∑ d : Fin n → Z2 L, SigmaPi L (mSig E) t σ π d *
          ∏ v, thetaEdge L (mSig E) t (σ v) (σ (v + 1)) (a v) (d v) := by
  intro L _ E t n _ σ a π
  simp only [Kpi, SigmaPi, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  exact treeValW_eq_sum_selfW L F a _ _

/-- **The symmetry `g(s) = g(-s)`** (after `(res_SIGempdd)`), for every `σ`:
`Σ^{(∅)}(t, σ, d₁ + s) = Σ^{(∅)}(t, σ, d₁ - s)` when `s₁ = 0`. -/
theorem SigmaPi_empty_symm :
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (n : ℕ) [NeZero n] (σ : Fin n → Bool) (d₁ : Z2 L) (s : Fin n → Z2 L), s 0 = 0 →
      SigmaPi L (mSig E) t σ ∅ (fun i => d₁ + s i)
        = SigmaPi L (mSig E) t σ ∅ (fun i => d₁ - s i) := by
  intro L _ hL E hE t ht n _ σ d₁ s _
  have hE2 : |E| ≤ 2 := hE.le
  have hx : (fun i => d₁ - s i) = fun i => (d₁ + d₁) - (d₁ + s i) :=
    funext fun i => by abel
  rw [hx]
  unfold SigmaPi
  refine Finset.sum_congr rfl fun F _ => ?_
  unfold selfE
  refine (selfW_reflect L F _ (d₁ + d₁) (fun e p q => ?_) (fun i => d₁ + s i)).symm
  have hξ : ‖(t : ℂ) * (mSig E (σ e.1.1) * mSig E (σ e.1.2))‖ < 1 := by
    rw [norm_xi hE2 ht.1]; exact ht.2
  simp only [Matrix.sub_apply, Matrix.one_apply, sub_right_inj, thetaEdge,
    Theta_reflect L hL hξ]

end Statements

end RBM.KLoop
