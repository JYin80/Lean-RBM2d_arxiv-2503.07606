/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Evolution.Case3Defs
import RBM2D.Evolution.LatticeSums
import RBM2D.Loop.LatticeCount
import RBM2D.Gauss.LoopEnvelope
import Mathlib.Analysis.Convex.Integral

/-!
# The moment and counting half of the `clt-lemma`

Paper: Section 7, `clt-lemma`, its moment expansion (`clt-lemmamoment`), the far decorrelation
claim (`clt-lemmafar`), the moment bound (`eq:cltmomentfinal`) and the two cases
(`clt-lemma-final-result`; `clt-lemma-final-result2`).  The paper's `s` is `u n` and its `t` is
`t n`.

* `CltFar` (`clt-lemmafar` as a hypothesis, proved in `CltDecorrelation.lean`);
* `cltMomentBound` (`eq:cltmomentfinal`): deterministic given the far bound; the cluster sum
  `CltMoments.clusterSum` is over free-index structures `(𝒮, φ)` (`CltMoments.Cluster`), with
  cluster radius `3 W^{2τ} ℓ_u` (a maximal `3R`-separated set of free indices, independent of `p`);
* `cltCase1_of_far`, `cltCase2_of_far`: `CltCase1Prec`, `CltCase2Prec` (`Case3Defs.lean`) with the
  three inputs `Step2LocalPT`, `Step2DecayPT`, `GbEXPHypV3` replaced by `CltFar`; the
  deterministic bound `‖Y‖_max ≤ (K+1) N^{C'} (2 N^3 / c_κ)^K` is proved here
  (`cltm_Y_bound`), with `c_κ = √(κ(4-κ))/2`.  Constants: `C ≥ 4` (Case 1), `C ≥ 2` (Case 2).

The `RBM.KLoop.card_ball_le` and `RBM.Evol.expInvSum` counts are used for the
`d = 2` lattice sums.  The matrix-inverse measurability is private.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

section Combinatorics

variable {L : ℕ} [NeZero L]

private theorem cltm_zdist_neg (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

private theorem cltm_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, cltm_zdist_neg]

private theorem cltm_zdist2_comm (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
  rw [← neg_sub, cltm_zdist2_neg]

private theorem cltm_zdist2_tri (x y z : Z2 L) :
    zdist2 L (x - z) ≤ zdist2 L (x - y) + zdist2 L (y - z) := by
  have := zdist2_add_le L (x - y) (y - z)
  simpa using this

/-- Free-index structure `(𝒮, assignment)` of a cluster in `eq:cltmomentfinal`: a
retraction `φ` of `Fin n` (`φ ∘ φ = φ`) whose fixed points (the free indices `𝒮`) each carry at
least one further index; `φ k` is the free index that `k` is assigned to. -/
def CltMoments.Cluster {n : ℕ} (φ : Fin n → Fin n) : Prop :=
  (∀ i, φ (φ i) = φ i) ∧ ∀ i, φ i = i → ∃ k, k ≠ i ∧ φ k = i

private theorem cltm_exists_cluster {n : ℕ} (b : Fin n → Z2 L) (R : ℝ)
    (hnf : ∀ i, ∃ k, k ≠ i ∧ (zdist2 L (b i - b k) : ℝ) < R) :
    ∃ φ : Fin n → Fin n, CltMoments.Cluster φ ∧ ∀ k, (zdist2 L (b (φ k) - b k) : ℝ) ≤ 3 * R := by
  classical
  set dd : Fin n → Fin n → ℝ := fun i k => (zdist2 L (b i - b k) : ℝ) with hdd
  have dsymm : ∀ i k, dd i k = dd k i := fun i k => by
    simp only [hdd]; rw [cltm_zdist2_comm]
  have dtri : ∀ i k m, dd i m ≤ dd i k + dd k m := fun i k m => by
    simp only [hdd]; exact_mod_cast cltm_zdist2_tri (b i) (b k) (b m)
  have dnn : ∀ i k, 0 ≤ dd i k := fun i k => by simp only [hdd]; positivity
  have dself : ∀ i, dd i i = 0 := fun i => by simp [hdd]
  let Sep : Finset (Fin n) → Prop := fun S => ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 3 * R ≤ dd s s'
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image (Finset.univ.filter Sep) Finset.card
    ⟨∅, by simp [Sep]⟩
  have hSep : Sep S := (Finset.mem_filter.1 hSmem).2
  have hmax : ∀ k, k ∉ S → ∃ s ∈ S, dd k s < 3 * R := by
    intro k hk
    by_contra hcon
    push Not at hcon
    have hsep' : Sep (insert k S) := by
      intro s hs s' hs' hne
      rcases Finset.mem_insert.1 hs with h1 | h1
      · rcases Finset.mem_insert.1 hs' with h2 | h2
        · exact absurd (h1.trans h2.symm) hne
        · rw [h1]; exact hcon s' h2
      · rcases Finset.mem_insert.1 hs' with h2 | h2
        · rw [h2, dsymm]; exact hcon s h1
        · exact hSep s h1 s' h2 hne
    have := hSmax (insert k S) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hsep'⟩)
    rw [Finset.card_insert_of_notMem hk] at this
    omega
  have hex : ∀ k, ∃ m, m ∈ S ∧ (k ∈ S → m = k) ∧ (k ∉ S → ∀ s' ∈ S, dd k m ≤ dd k s') := by
    intro k
    by_cases hk : k ∈ S
    · exact ⟨k, hk, fun _ => rfl, fun h => absurd hk h⟩
    · obtain ⟨s, hs, _⟩ := hmax k hk
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image S (dd k) ⟨s, hs⟩
      exact ⟨m, hm, fun h => absurd h hk, fun _ => hmin⟩
  choose φ hφS hφfix hφmin using hex
  refine ⟨φ, ⟨fun i => hφfix (φ i) (hφS i), ?_⟩, ?_⟩
  · intro i hi
    have hiS : i ∈ S := hi ▸ hφS i
    obtain ⟨k₀, hk₀ne, hk₀d⟩ := hnf i
    have hRpos : 0 < R := lt_of_le_of_lt (dnn i k₀) hk₀d
    have hk₀S : k₀ ∉ S := by
      intro hk₀S
      have := hSep i hiS k₀ hk₀S (Ne.symm hk₀ne)
      change 3 * R ≤ dd i k₀ at this
      change dd i k₀ < R at hk₀d
      linarith
    refine ⟨k₀, hk₀ne, ?_⟩
    by_contra hne
    have h1 : dd k₀ (φ k₀) ≤ dd k₀ i := hφmin k₀ hk₀S i hiS
    have h2 : dd i k₀ < R := hk₀d
    have h3 := hSep i hiS (φ k₀) (hφS k₀) (Ne.symm hne)
    have h4 := dtri i k₀ (φ k₀)
    have := dsymm k₀ i
    linarith
  · intro k
    by_cases hk : k ∈ S
    · have : φ k = k := hφfix k hk
      rw [this]
      have := dself k
      have hRpos : 0 < R := by
        obtain ⟨k₀, _, hk₀d⟩ := hnf k
        exact lt_of_le_of_lt (dnn k k₀) hk₀d
      change dd k k ≤ 3 * R
      linarith
    · obtain ⟨s, hs, hsd⟩ := hmax k hk
      have h1 := hφmin k hk s hs
      have h2 := dsymm (φ k) k
      change dd (φ k) k ≤ 3 * R
      linarith


/-- The number of non-free indices assigned to the free index `s`. -/
def CltMoments.assigned {n : ℕ} (φ : Fin n → Fin n) (s : Fin n) : ℕ :=
  (Finset.univ.filter fun k => φ k = s ∧ k ≠ s).card

/-- The closed ball `{β' : |β - β'|_L ≤ R}`. -/
def CltMoments.ball (L : ℕ) [NeZero L] (R : ℝ) (β : Z2 L) : Finset (Z2 L) :=
  Finset.univ.filter fun β' => (zdist2 L (β - β') : ℝ) ≤ R

open Classical in
/-- The cluster sum
`𝒞_p(z, R') = Σ_{(𝒮,φ)} ∏_{s∈𝒮} Σ_β z_β (Σ_{|β'-β|_L ≤ R'} z_{β'})^{k_s}`
of `eq:cltmomentfinal`, over the cluster structures `(𝒮, φ)` (`CltMoments.Cluster`) on
`n` indices, `k_s = CltMoments.assigned φ s`. -/
def CltMoments.clusterSum (L : ℕ) [NeZero L] (n : ℕ) (z : Z2 L → ℝ) (R : ℝ) : ℝ :=
  ∑ φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMoments.Cluster φ),
    ∏ s ∈ Finset.univ.filter (fun s => φ s = s),
      ∑ β : Z2 L, z β * (∑ β' ∈ CltMoments.ball L R β, z β') ^ CltMoments.assigned φ s

private theorem cltm_sum_compat {n : ℕ} (φ : Fin n → Fin n) (hφ : φ ∘ φ = φ) (z : Z2 L → ℝ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin n → Z2 L =>
        ∀ k, (zdist2 L (b (φ k) - b k) : ℝ) ≤ R), ∏ k, z (b k)
      = ∏ s ∈ Finset.univ.filter (fun s => φ s = s),
          ∑ β : Z2 L, z β * (∑ β' ∈ CltMoments.ball L R β, z β') ^ CltMoments.assigned φ s := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun s => φ s = s) with hS
  have hφS : ∀ k, φ k ∈ S := fun k => by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact congrFun hφ k
  let t : Fin n → Finset (Z2 L) := fun k => if k ∈ S then Finset.univ else {0}
  let r : (Fin n → Z2 L) → (Fin n → Z2 L) := fun b k => if k ∈ S then b k else 0
  set C : Finset (Fin n → Z2 L) := Finset.univ.filter (fun b : Fin n → Z2 L =>
        ∀ k, (zdist2 L (b (φ k) - b k) : ℝ) ≤ R) with hC
  have hmaps : ∀ b ∈ C, r b ∈ Fintype.piFinset t := by
    intro b _
    rw [Fintype.mem_piFinset]
    intro k
    by_cases hk : k ∈ S
    · simp [r, t, hk]
    · simp [r, t, hk]
  rw [← Finset.sum_fiberwise_of_maps_to (g := r) (t := Fintype.piFinset t) hmaps]
  set Bf : Z2 L → ℝ := fun β => ∑ β' ∈ CltMoments.ball L R β, z β' with hBf
  have hfib : ∀ β ∈ Fintype.piFinset t,
      ∑ b ∈ C with r b = β, ∏ k, z (b k)
        = ∏ s ∈ S, z (β s) * Bf (β s) ^ CltMoments.assigned φ s := by
    intro β hβ
    have hβ' : ∀ k, k ∉ S → β k = 0 := by
      intro k hk
      have := Fintype.mem_piFinset.1 hβ k
      simpa [t, hk] using this
    have hset : C.filter (fun b => r b = β) =
        Fintype.piFinset (fun k => if k ∈ S then {β k} else CltMoments.ball L R (β (φ k))) := by
      ext b
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨hcomp, hrb⟩ k
        by_cases hk : k ∈ S
        · have : r b k = β k := congrFun hrb k
          simp only [r, hk, ite_true] at this
          simp [hk, this]
        · have hφk : b (φ k) = β (φ k) := by
            have : r b (φ k) = β (φ k) := congrFun hrb (φ k)
            simpa [r, hφS k] using this
          simp only [hk, ite_false, CltMoments.ball, Finset.mem_filter, Finset.mem_univ, true_and]
          have := hcomp k
          rw [hφk] at this
          exact this
      · intro hb
        refine ⟨?_, ?_⟩
        · intro k
          by_cases hk : k ∈ S
          · have hbk : b k = β k := by simpa [hk] using hb k
            have hφk : φ k = k := (Finset.mem_filter.1 hk).2
            rw [hφk]; simpa using hR
          · have hbk := hb k
            simp only [hk, ite_false, CltMoments.ball, Finset.mem_filter, Finset.mem_univ, true_and] at hbk
            have hφk : b (φ k) = β (φ k) := by
              have := hb (φ k)
              simpa [hφS k] using this
            rw [hφk]; exact hbk
        · funext k
          by_cases hk : k ∈ S
          · have hbk : b k = β k := by simpa [hk] using hb k
            simp [r, hk, hbk]
          · simp [r, hk, hβ' k hk]
    rw [hset, ← Finset.prod_univ_sum (fun k => if k ∈ S then ({β k} : Finset (Z2 L)) else CltMoments.ball L R (β (φ k)))
      (fun _ x => z x)]
    have h1 : ∏ k, ∑ x ∈ (if k ∈ S then ({β k} : Finset (Z2 L)) else CltMoments.ball L R (β (φ k))), z x
        = ∏ k, (if k ∈ S then z (β k) else Bf (β (φ k))) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hk : k ∈ S <;> simp [hk, hBf]
    rw [h1, Finset.prod_ite]
    have e1 : (Finset.univ.filter fun k => k ∈ S) = S := by ext; simp
    have e2 : (Finset.univ.filter fun k => k ∉ S) = Sᶜ := by ext; simp
    rw [e1, e2]
    have e3 : ∏ k ∈ Sᶜ, Bf (β (φ k)) = ∏ s ∈ S, Bf (β s) ^ CltMoments.assigned φ s := by
      rw [← Finset.prod_fiberwise_of_maps_to (g := φ) (t := S) (f := fun k => Bf (β (φ k)))
        (fun k _ => hφS k)]
      refine Finset.prod_congr rfl fun y hy => ?_
      have hfil : (Sᶜ.filter fun k => φ k = y) = Finset.univ.filter fun k => φ k = y ∧ k ≠ y := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hk, hky⟩
          exact ⟨hky, fun h => hk (h ▸ hy)⟩
        · rintro ⟨hky, hne⟩
          refine ⟨fun hk => hne ?_, hky⟩
          have : φ k = k := (Finset.mem_filter.1 hk).2
          rw [← this, hky]
      have : ∏ k ∈ Sᶜ.filter (fun k => φ k = y), Bf (β (φ k)) = ∏ k ∈ Sᶜ.filter (fun k => φ k = y), Bf (β y) :=
        Finset.prod_congr rfl fun k hk => by rw [(Finset.mem_filter.1 hk).2]
      rw [this, Finset.prod_const, hfil]
      rfl
    rw [e3, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl hfib]
  -- now sum over β ∈ piFinset t of ∏_{s ∈ S} h s (β s)
  let h : Fin n → Z2 L → ℝ := fun k x => if k ∈ S then z x * Bf x ^ CltMoments.assigned φ k else 1
  have hsum := Finset.prod_univ_sum t h
  have h2 : ∀ β : Fin n → Z2 L, ∏ k, h k (β k) = ∏ s ∈ S, z (β s) * Bf (β s) ^ CltMoments.assigned φ s := by
    intro β
    simp only [h]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    have e1 : (Finset.univ.filter fun k => k ∈ S) = S := by ext; simp
    rw [e1]
  simp only [h2] at hsum
  rw [← hsum]
  have h3 : ∀ k, ∑ x ∈ t k, h k x = if k ∈ S then ∑ β : Z2 L, z β * Bf β ^ CltMoments.assigned φ k else 1 := by
    intro k
    by_cases hk : k ∈ S <;> simp [t, h, hk]
  rw [Finset.prod_congr rfl fun k _ => h3 k, Finset.prod_ite, Finset.prod_const_one, mul_one]
  have e1 : (Finset.univ.filter fun k => k ∈ S) = S := by ext; simp
  rw [e1]

private theorem cltm_nonfar_sum_le {n : ℕ} (z : Z2 L → ℝ) (hz : ∀ β, 0 ≤ z β) (R : ℝ)
    (hR : 0 ≤ R) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin n → Z2 L =>
        ∀ i, ∃ k, k ≠ i ∧ (zdist2 L (b i - b k) : ℝ) < R), ∏ k, z (b k)
      ≤ CltMoments.clusterSum L n z (3 * R) := by
  classical
  have hR3 : 0 ≤ 3 * R := by linarith
  unfold CltMoments.clusterSum
  have hstep : ∀ φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMoments.Cluster φ),
      ∏ s ∈ Finset.univ.filter (fun s => φ s = s),
        ∑ β : Z2 L, z β * (∑ β' ∈ CltMoments.ball L (3 * R) β, z β') ^ CltMoments.assigned φ s
      = ∑ b : Fin n → Z2 L, if (∀ k, (zdist2 L (b (φ k) - b k) : ℝ) ≤ 3 * R)
          then ∏ k, z (b k) else 0 := by
    intro φ hφ
    have hφ' : CltMoments.Cluster φ := (Finset.mem_filter.1 hφ).2
    have hcomp : φ ∘ φ = φ := funext hφ'.1
    rw [← cltm_sum_compat φ hcomp z (3 * R) hR3, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  set G : (Fin n → Z2 L) → ℝ := fun b => ∑ φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter
    (fun φ => CltMoments.Cluster φ), if (∀ k, (zdist2 L (b (φ k) - b k) : ℝ) ≤ 3 * R)
      then ∏ k, z (b k) else 0 with hG
  have hwnn : ∀ b : Fin n → Z2 L, 0 ≤ ∏ k, z (b k) := fun b => Finset.prod_nonneg fun k _ => hz _
  have hG0 : ∀ b, 0 ≤ G b := fun b =>
    Finset.sum_nonneg fun φ _ => by split_ifs; exacts [hwnn b, le_rfl]
  have hG1 : ∀ b : Fin n → Z2 L, (∀ i, ∃ k, k ≠ i ∧ (zdist2 L (b i - b k) : ℝ) < R) →
      ∏ k, z (b k) ≤ G b := by
    intro b hb
    obtain ⟨φ, hφ, hφd⟩ := cltm_exists_cluster b R hb
    have hmem : φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMoments.Cluster φ) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hφ⟩
    have hsingle := Finset.single_le_sum (f := fun φ : Fin n → Fin n =>
      if (∀ k, (zdist2 L (b (φ k) - b k) : ℝ) ≤ 3 * R) then ∏ k, z (b k) else 0)
      (s := (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMoments.Cluster φ))
      (fun φ _ => by split_ifs; exacts [hwnn b, le_rfl]) hmem
    have hite : (if (∀ k, (zdist2 L (b (φ k) - b k) : ℝ) ≤ 3 * R) then ∏ k, z (b k) else 0)
        = ∏ k, z (b k) := by simp [hφd]
    rw [hite] at hsingle
    exact hsingle
  calc ∑ b ∈ Finset.univ.filter (fun b : Fin n → Z2 L =>
        ∀ i, ∃ k, k ≠ i ∧ (zdist2 L (b i - b k) : ℝ) < R), ∏ k, z (b k)
      ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin n → Z2 L =>
        ∀ i, ∃ k, k ≠ i ∧ (zdist2 L (b i - b k) : ℝ) < R), G b :=
        Finset.sum_le_sum fun b hb => hG1 b (Finset.mem_filter.1 hb).2
    _ ≤ ∑ b : Fin n → Z2 L, G b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ => hG0 b

/-- The free indices of `φ`. -/
private abbrev cltFree {n : ℕ} (φ : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun s => φ s = s)

private theorem cltm_assigned_pos {n : ℕ} {φ : Fin n → Fin n} (hφ : CltMoments.Cluster φ) {s : Fin n}
    (hs : φ s = s) : 1 ≤ CltMoments.assigned φ s := by
  obtain ⟨k, hk, hks⟩ := hφ.2 s hs
  unfold CltMoments.assigned
  exact Finset.card_pos.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hks, hk⟩⟩

private theorem cltm_sum_assigned {n : ℕ} {φ : Fin n → Fin n} (hφ : CltMoments.Cluster φ) :
    ∑ s ∈ cltFree φ, CltMoments.assigned φ s + (cltFree φ).card = n := by
  classical
  have hmaps : Set.MapsTo φ ((cltFree φ)ᶜ : Finset (Fin n)) (cltFree φ : Finset (Fin n)) := by
    intro k _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact hφ.1 k
  have h1 := Finset.card_eq_sum_card_fiberwise hmaps
  have h2 : ∀ y ∈ cltFree φ, ((cltFree φ)ᶜ.filter fun a => φ a = y).card = CltMoments.assigned φ y := by
    intro y hy
    have hyS : φ y = y := (Finset.mem_filter.1 hy).2
    unfold CltMoments.assigned
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hk, hky⟩
      refine ⟨hky, fun h => hk ?_⟩
      rw [h]; exact hyS
    · rintro ⟨hky, hne⟩
      refine ⟨fun hk => hne ?_, hky⟩
      have : φ k = k := hk
      rw [← this, hky]
  rw [Finset.sum_congr rfl h2] at h1
  have h3 := Finset.card_compl (cltFree φ)
  simp only [Fintype.card_fin] at h3
  have : (cltFree φ).card ≤ n := by
    have := Finset.card_le_univ (cltFree φ); simpa using this
  have h1' : ((cltFree φ)ᶜ).card = ∑ s ∈ cltFree φ, CltMoments.assigned φ s := h1
  omega

private theorem cltm_two_mul_free_le {n : ℕ} {φ : Fin n → Fin n} (hφ : CltMoments.Cluster φ) :
    2 * (cltFree φ).card ≤ n := by
  have h := cltm_sum_assigned hφ
  have h2 : (cltFree φ).card ≤ ∑ s ∈ cltFree φ, CltMoments.assigned φ s := by
    calc (cltFree φ).card = ∑ _s ∈ cltFree φ, 1 := by simp
      _ ≤ ∑ s ∈ cltFree φ, CltMoments.assigned φ s :=
        Finset.sum_le_sum fun s hs => cltm_assigned_pos hφ (Finset.mem_filter.1 hs).2
  omega

open Classical in
private theorem cltm_card_cluster_le (n : ℕ) :
    (((Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMoments.Cluster φ)).card : ℝ)
      ≤ (n : ℝ) ^ n := by
  classical
  have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin n → Fin n)) (fun φ => CltMoments.Cluster φ)
  have h2 : (Finset.univ : Finset (Fin n → Fin n)).card = n ^ n := by
    simp [Finset.card_univ]
  have : ((Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMoments.Cluster φ)).card ≤ n ^ n := by
    omega
  exact_mod_cast this

/-- General reduction: a bound `g κ` on the per-cluster sums bounds the cluster sum. -/
private theorem cltm_clusterSum_le_of_bound {n : ℕ} (z : Z2 L → ℝ) (hz0 : ∀ β, 0 ≤ z β) (R : ℝ)
    (g : ℕ → ℝ) (hg : ∀ k, 1 ≤ k → ∑ β, z β * (∑ β' ∈ CltMoments.ball L R β, z β') ^ k ≤ g k)
    (Bnd : ℝ) (hBnd0 : 0 ≤ Bnd)
    (hprod : ∀ φ : Fin n → Fin n, CltMoments.Cluster φ → ∏ s ∈ cltFree φ, g (CltMoments.assigned φ s) ≤ Bnd) :
    CltMoments.clusterSum L n z R ≤ (n : ℝ) ^ n * Bnd := by
  classical
  unfold CltMoments.clusterSum
  calc ∑ φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMoments.Cluster φ),
        ∏ s ∈ Finset.univ.filter (fun s => φ s = s),
          ∑ β : Z2 L, z β * (∑ β' ∈ CltMoments.ball L R β, z β') ^ CltMoments.assigned φ s
      ≤ ∑ _φ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMoments.Cluster φ), Bnd := by
        refine Finset.sum_le_sum fun φ hφ => ?_
        have hφ' : CltMoments.Cluster φ := (Finset.mem_filter.1 hφ).2
        refine le_trans (Finset.prod_le_prod₀ (fun s _ => Finset.sum_nonneg fun β _ =>
          mul_nonneg (hz0 β) (pow_nonneg (Finset.sum_nonneg fun β' _ => hz0 β') _))
          (fun s hs => hg _ (cltm_assigned_pos hφ' (Finset.mem_filter.1 hs).2))) (hprod φ hφ')
    _ = (((Finset.univ : Finset (Fin n → Fin n)).filter (fun φ => CltMoments.Cluster φ)).card : ℝ) * Bnd := by
        simp
    _ ≤ (n : ℝ) ^ n * Bnd := mul_le_mul_of_nonneg_right (cltm_card_cluster_le n) hBnd0

private theorem cltm_ball_sum_le (z : Z2 L → ℝ) (hz0 : ∀ β, 0 ≤ z β) (M : ℝ) (hM : ∀ β, z β ≤ M)
    (R' : ℝ) (hR' : 0 ≤ R') (β : Z2 L) :
    ∑ β' ∈ CltMoments.ball L R' β, z β' ≤ M * (2 * R' + 1) ^ 2 := by
  calc ∑ β' ∈ CltMoments.ball L R' β, z β' ≤ ∑ _β' ∈ CltMoments.ball L R' β, M :=
        Finset.sum_le_sum fun β' _ => hM β'
    _ = (CltMoments.ball L R' β).card * M := by simp
    _ ≤ (2 * R' + 1) ^ 2 * M := by
        have hM0 : 0 ≤ M := (hz0 0).trans (hM 0)
        exact mul_le_mul_of_nonneg_right (RBM.KLoop.card_ball_le L β R' hR') hM0
    _ = M * (2 * R' + 1) ^ 2 := by ring

private theorem cltm_T1 (z : Z2 L → ℝ) (hz0 : ∀ β, 0 ≤ z β) (M : ℝ) (hM : ∀ β, z β ≤ M)
    (a : Z2 L) (ρ : ℝ) (hρ : 0 ≤ ρ) (hsupp : ∀ β, ρ ≤ (zdist2 L (a - β) : ℝ) → z β = 0)
    (R' : ℝ) (hR' : 0 ≤ R') (k : ℕ) :
    ∑ β, z β * (∑ β' ∈ CltMoments.ball L R' β, z β') ^ k ≤
      M ^ (k + 1) * ((2 * ρ + 1) ^ 2 * ((2 * R' + 1) ^ 2) ^ k) := by
  have hM0 : 0 ≤ M := (hz0 0).trans (hM 0)
  have hball := fun β => cltm_ball_sum_le z hz0 M hM R' hR' β
  have hpow : ∀ β, (∑ β' ∈ CltMoments.ball L R' β, z β') ^ k ≤ (M * (2 * R' + 1) ^ 2) ^ k := fun β =>
    pow_le_pow_left₀ (Finset.sum_nonneg fun β' _ => hz0 β') (hball β) k
  have hsum : ∑ β, z β ≤ M * (2 * ρ + 1) ^ 2 := by
    calc ∑ β, z β ≤ ∑ β, (if (zdist2 L (a - β) : ℝ) ≤ ρ then M else 0) := by
          refine Finset.sum_le_sum fun β _ => ?_
          by_cases h : (zdist2 L (a - β) : ℝ) ≤ ρ
          · simp only [h, ite_true]; exact hM β
          · simp only [h, ite_false]; exact (hsupp β (le_of_not_ge h)) ▸ le_rfl
      _ = (Finset.univ.filter fun β : Z2 L => (zdist2 L (a - β) : ℝ) ≤ ρ).card * M := by
          rw [← Finset.sum_filter]; simp
      _ ≤ (2 * ρ + 1) ^ 2 * M :=
          mul_le_mul_of_nonneg_right (RBM.KLoop.card_ball_le L a ρ hρ) hM0
      _ = M * (2 * ρ + 1) ^ 2 := by ring
  calc ∑ β, z β * (∑ β' ∈ CltMoments.ball L R' β, z β') ^ k
      ≤ ∑ β, z β * (M * (2 * R' + 1) ^ 2) ^ k :=
        Finset.sum_le_sum fun β _ => mul_le_mul_of_nonneg_left (hpow β) (hz0 β)
    _ = (∑ β, z β) * (M * (2 * R' + 1) ^ 2) ^ k := by rw [Finset.sum_mul]
    _ ≤ (M * (2 * ρ + 1) ^ 2) * (M * (2 * R' + 1) ^ 2) ^ k :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = M ^ (k + 1) * ((2 * ρ + 1) ^ 2 * ((2 * R' + 1) ^ 2) ^ k) := by
        rw [mul_pow]; ring

/-- Case 1 cluster count. -/
private theorem cltm_clusterSum_case1 (p : ℕ) (z : Z2 L → ℝ) (hz0 : ∀ β, 0 ≤ z β) (M : ℝ)
    (hM : ∀ β, z β ≤ M) (a : Z2 L) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hsupp : ∀ β, ρ ≤ (zdist2 L (a - β) : ℝ) → z β = 0)
    (R' : ℝ) (hR' : 1 ≤ R') (u : ℝ) (hu1 : (3 * ρ) * (3 * R') ≤ u) (hu2 : (3 * R') ^ 2 ≤ u) :
    CltMoments.clusterSum L (2 * p) z R' ≤ ((2 * p : ℕ) : ℝ) ^ (2 * p) * (M * u) ^ (2 * p) := by
  have hM0 : 0 ≤ M := (hz0 0).trans (hM 0)
  have hρ0 : 0 ≤ ρ := by linarith
  have hR0 : 0 ≤ R' := by linarith
  have hu0 : 0 ≤ u := le_trans (by positivity) hu1
  have hA : (2 * ρ + 1) ^ 2 ≤ (3 * ρ) ^ 2 := by nlinarith
  have hBk : (2 * R' + 1) ^ 2 ≤ (3 * R') ^ 2 := by nlinarith
  refine cltm_clusterSum_le_of_bound z hz0 R'
    (fun k => M ^ (k + 1) * ((2 * ρ + 1) ^ 2 * ((2 * R' + 1) ^ 2) ^ k))
    (fun k _ => cltm_T1 z hz0 M hM a ρ hρ0 hsupp R' hR0 k) ((M * u) ^ (2 * p)) (by positivity) ?_
  intro φ hφ
  have hsum := cltm_sum_assigned hφ
  have hhalf := cltm_two_mul_free_le hφ
  set j := (cltFree φ).card with hj
  set K := ∑ s ∈ cltFree φ, CltMoments.assigned φ s with hK
  have hprod : ∏ s ∈ cltFree φ, (M ^ (CltMoments.assigned φ s + 1) *
      ((2 * ρ + 1) ^ 2 * ((2 * R' + 1) ^ 2) ^ CltMoments.assigned φ s))
      = M ^ (2 * p) * (((2 * ρ + 1) ^ 2) ^ j * ((2 * R' + 1) ^ 2) ^ K) := by
    have hM' : ∏ s ∈ cltFree φ, M ^ (CltMoments.assigned φ s + 1) = M ^ (2 * p) := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      omega
    have hA' : ∏ _s ∈ cltFree φ, (2 * ρ + 1) ^ 2 = ((2 * ρ + 1) ^ 2) ^ j := by
      rw [Finset.prod_const]
    have hB' : ∏ s ∈ cltFree φ, ((2 * R' + 1) ^ 2) ^ CltMoments.assigned φ s
        = ((2 * R' + 1) ^ 2) ^ K := Finset.prod_pow_eq_pow_sum _ _ _
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hM', hA', hB']
  rw [hprod]
  have hb : ((2 * ρ + 1) ^ 2) ^ j * ((2 * R' + 1) ^ 2) ^ K ≤ u ^ (2 * p) := by
    calc ((2 * ρ + 1) ^ 2) ^ j * ((2 * R' + 1) ^ 2) ^ K
        ≤ ((3 * ρ) ^ 2) ^ j * ((3 * R') ^ 2) ^ K := by gcongr
      _ = ((3 * ρ) * (3 * R')) ^ (2 * j) * ((3 * R') ^ 2) ^ (2 * p - 2 * j) := by
          have key : ∀ a c : ℝ, ∀ j m : ℕ, (a ^ 2) ^ j * (c ^ 2) ^ (j + m)
              = (a * c) ^ (2 * j) * (c ^ 2) ^ m := by intros; ring
          have hK2 : K = j + (2 * p - 2 * j) := by omega
          rw [hK2]
          exact key _ _ _ _
      _ ≤ u ^ (2 * j) * u ^ (2 * p - 2 * j) := by gcongr
      _ = u ^ (2 * p) := by rw [← pow_add]; congr 1; omega
  calc M ^ (2 * p) * (((2 * ρ + 1) ^ 2) ^ j * ((2 * R' + 1) ^ 2) ^ K) ≤ M ^ (2 * p) * u ^ (2 * p) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (M * u) ^ (2 * p) := by rw [mul_pow]

/-- The Case 2 weight `f_a(β) = (|a - β|_L + 1)⁻¹`. -/
private def cltFw (a : Z2 L) (β : Z2 L) : ℝ := ((zdist2 L (a - β) : ℝ) + 1)⁻¹

private theorem cltFw_pos (a β : Z2 L) : 0 < cltFw a β := by
  unfold cltFw; positivity

private theorem cltFw_le_one (a β : Z2 L) : cltFw a β ≤ 1 := by
  unfold cltFw
  refine inv_le_one_of_one_le₀ ?_
  have : (0 : ℝ) ≤ zdist2 L (a - β) := Nat.cast_nonneg _
  linarith

private theorem cltm_sum_f_sq (hL : 3 ≤ L) (a : Z2 L) :
    ∑ β, cltFw a β ^ 2 ≤ 5 + 4 * Real.log L := by
  refine le_trans (Finset.sum_le_sum fun β _ => ?_) (RBM.KLoop.sum_inv_sq_le L hL a)
  unfold cltFw
  rw [inv_pow]
  refine inv_anti₀ (by positivity) ?_
  have : (0 : ℝ) ≤ zdist2 L (a - β) := Nat.cast_nonneg _
  nlinarith

private theorem cltm_ball_f_le (hL : 3 ≤ L) (a : Z2 L) (R' : ℝ) (hR' : 0 < R') (β : Z2 L) :
    ∑ β' ∈ CltMoments.ball L R' β, cltFw a β' ≤
      Real.exp 1 * ((1 + R') * Real.sqrt (5 + 4 * Real.log L)) := by
  have h := expInvSum L hL R' hR' β a
  calc ∑ β' ∈ CltMoments.ball L R' β, cltFw a β'
      = ∑ b, if (zdist2 L (β - b) : ℝ) ≤ R' then cltFw a b else 0 := by
        rw [CltMoments.ball, Finset.sum_filter]
    _ ≤ ∑ b, Real.exp 1 * (Real.exp (-(zdist2 L (b - β) : ℝ) / R') /
          ((zdist2 L (b - a) : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [cltm_zdist2_comm β b]
        have hfb : cltFw a b = ((zdist2 L (b - a) : ℝ) + 1)⁻¹ := by
          unfold cltFw; rw [cltm_zdist2_comm a b]
        by_cases hb : (zdist2 L (b - β) : ℝ) ≤ R'
        · simp only [hb, ite_true]
          rw [hfb, ← mul_div_assoc, div_eq_mul_inv]
          have hexp : 1 ≤ Real.exp 1 * Real.exp (-(zdist2 L (b - β) : ℝ) / R') := by
            rw [← Real.exp_add]
            apply Real.one_le_exp
            have : (zdist2 L (b - β) : ℝ) / R' ≤ 1 := (div_le_one hR').2 hb
            rw [neg_div]; linarith
          have hinv : 0 ≤ ((zdist2 L (b - a) : ℝ) + 1)⁻¹ := by positivity
          nlinarith
        · simp only [hb, ite_false]
          positivity
    _ = Real.exp 1 * ∑ b, Real.exp (-(zdist2 L (b - β) : ℝ) / R') /
          ((zdist2 L (b - a) : ℝ) + 1) := by rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * ((1 + R') * Real.sqrt (5 + 4 * Real.log L)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le

private theorem cltm_double_sum (hL : 3 ≤ L) (a : Z2 L) (R' : ℝ) (hR' : 0 ≤ R') :
    ∑ β, cltFw a β * ∑ β' ∈ CltMoments.ball L R' β, cltFw a β' ≤
      (2 * R' + 1) ^ 2 * (5 + 4 * Real.log L) := by
  have hcard : ∀ β, ((CltMoments.ball L R' β).card : ℝ) ≤ (2 * R' + 1) ^ 2 := fun β =>
    RBM.KLoop.card_ball_le L β R' hR'
  have hsq := cltm_sum_f_sq hL a
  have hN0 : (0 : ℝ) ≤ (2 * R' + 1) ^ 2 := by positivity
  calc ∑ β, cltFw a β * ∑ β' ∈ CltMoments.ball L R' β, cltFw a β'
      = ∑ β, ∑ β' ∈ CltMoments.ball L R' β, cltFw a β * cltFw a β' := by
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ β, ∑ β' ∈ CltMoments.ball L R' β, (cltFw a β ^ 2 / 2 + cltFw a β' ^ 2 / 2) := by
        refine Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun β' _ => ?_
        nlinarith [sq_nonneg (cltFw a β - cltFw a β')]
    _ = ∑ β, ∑ β' ∈ CltMoments.ball L R' β, cltFw a β ^ 2 / 2 +
          ∑ β, ∑ β' ∈ CltMoments.ball L R' β, cltFw a β' ^ 2 / 2 := by
        simp_rw [Finset.sum_add_distrib]
    _ ≤ (2 * R' + 1) ^ 2 * (5 + 4 * Real.log L) / 2 + (2 * R' + 1) ^ 2 * (5 + 4 * Real.log L) / 2 := by
        gcongr
        · calc ∑ β, ∑ β' ∈ CltMoments.ball L R' β, cltFw a β ^ 2 / 2
              = ∑ β, ((CltMoments.ball L R' β).card : ℝ) * (cltFw a β ^ 2 / 2) := by
                simp
            _ ≤ ∑ β, (2 * R' + 1) ^ 2 * (cltFw a β ^ 2 / 2) :=
                Finset.sum_le_sum fun β _ => mul_le_mul_of_nonneg_right (hcard β) (by positivity)
            _ = (2 * R' + 1) ^ 2 / 2 * ∑ β, cltFw a β ^ 2 := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun β _ => by ring
            _ ≤ (2 * R' + 1) ^ 2 / 2 * (5 + 4 * Real.log L) :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
            _ = (2 * R' + 1) ^ 2 * (5 + 4 * Real.log L) / 2 := by ring
        · have hswap : ∑ β, ∑ β' ∈ CltMoments.ball L R' β, cltFw a β' ^ 2 / 2 =
              ∑ β', ((Finset.univ.filter fun β : Z2 L => (zdist2 L (β - β') : ℝ) ≤ R').card : ℝ) *
                (cltFw a β' ^ 2 / 2) := by
            simp only [CltMoments.ball, Finset.sum_filter]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun β' _ => ?_
            rw [← Finset.sum_filter]
            simp
          have hfil : ∀ β' : Z2 L, (Finset.univ.filter fun β : Z2 L => (zdist2 L (β - β') : ℝ) ≤ R')
              = CltMoments.ball L R' β' := by
            intro β'
            ext β
            simp only [CltMoments.ball, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [cltm_zdist2_comm β β']
          rw [hswap]
          calc ∑ β', ((Finset.univ.filter fun β : Z2 L => (zdist2 L (β - β') : ℝ) ≤ R').card : ℝ) *
                (cltFw a β' ^ 2 / 2)
              ≤ ∑ β', (2 * R' + 1) ^ 2 * (cltFw a β' ^ 2 / 2) :=
                Finset.sum_le_sum fun β' _ => by
                  rw [hfil β']
                  exact mul_le_mul_of_nonneg_right (hcard β') (by positivity)
            _ = (2 * R' + 1) ^ 2 / 2 * ∑ β, cltFw a β ^ 2 := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun β _ => by ring
            _ ≤ (2 * R' + 1) ^ 2 / 2 * (5 + 4 * Real.log L) :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
            _ = (2 * R' + 1) ^ 2 * (5 + 4 * Real.log L) / 2 := by ring
    _ = (2 * R' + 1) ^ 2 * (5 + 4 * Real.log L) := by ring

private theorem cltm_T2 (hL : 3 ≤ L) (z : Z2 L → ℝ) (hz0 : ∀ β, 0 ≤ z β) (V : ℝ) (hV : 0 ≤ V)
    (a : Z2 L) (hz : ∀ β, z β ≤ V * cltFw a β) (R' : ℝ) (hR' : 1 ≤ R') (k : ℕ) (hk : 1 ≤ k) :
    ∑ β, z β * (∑ β' ∈ CltMoments.ball L R' β, z β') ^ k ≤
      (9 * V * R' * Real.sqrt (5 + 4 * Real.log L)) ^ (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  set Λ : ℝ := 5 + 4 * Real.log L with hΛ
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; linarith
  set lam : ℝ := Real.sqrt Λ with hlam
  have hlam0 : 0 ≤ lam := Real.sqrt_nonneg _
  have hlam2 : lam ^ 2 = Λ := Real.sq_sqrt hΛ0
  have hR0 : 0 < R' := by linarith
  set E : ℝ := Real.exp 1 * ((1 + R') * lam) with hE
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hE6 : E ≤ 6 * R' * lam := by
    rw [hE]
    have h1 : (1 + R') * lam ≤ 2 * R' * lam := by nlinarith
    calc Real.exp 1 * ((1 + R') * lam) ≤ 3 * (2 * R' * lam) :=
          mul_le_mul he3 h1 (by positivity) (by norm_num)
      _ = 6 * R' * lam := by ring
  set x : ℝ := 9 * V * R' * lam with hx
  have hx0 : 0 ≤ x := by positivity
  have hB : ∀ β, ∑ β' ∈ CltMoments.ball L R' β, z β' ≤ V * ∑ β' ∈ CltMoments.ball L R' β, cltFw a β' := by
    intro β
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun β' _ => hz β'
  have hBE : ∀ β, ∑ β' ∈ CltMoments.ball L R' β, z β' ≤ V * E := fun β =>
    (hB β).trans (mul_le_mul_of_nonneg_left (cltm_ball_f_le hL a R' hR0 β) hV)
  have hVE : V * E ≤ x := by
    calc V * E ≤ V * (6 * R' * lam) := mul_le_mul_of_nonneg_left hE6 hV
      _ ≤ 9 * V * R' * lam := by nlinarith [mul_nonneg (mul_nonneg hV hR0.le) hlam0]
  have hBnn : ∀ β, 0 ≤ ∑ β' ∈ CltMoments.ball L R' β, z β' := fun β =>
    Finset.sum_nonneg fun β' _ => hz0 β'
  have hpow : ∀ β, (∑ β' ∈ CltMoments.ball L R' β, z β') ^ m ≤ x ^ m := fun β =>
    pow_le_pow_left₀ (hBnn β) ((hBE β).trans hVE) m
  have hS : ∑ β, z β * ∑ β' ∈ CltMoments.ball L R' β, z β' ≤ x ^ 2 := by
    calc ∑ β, z β * ∑ β' ∈ CltMoments.ball L R' β, z β'
        ≤ ∑ β, (V * cltFw a β) * (V * ∑ β' ∈ CltMoments.ball L R' β, cltFw a β') :=
          Finset.sum_le_sum fun β _ => mul_le_mul (hz β) (hB β) (hBnn β)
            (mul_nonneg hV (cltFw_pos a β).le)
      _ = V ^ 2 * ∑ β, cltFw a β * ∑ β' ∈ CltMoments.ball L R' β, cltFw a β' := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun β _ => by ring
      _ ≤ V ^ 2 * ((2 * R' + 1) ^ 2 * Λ) :=
          mul_le_mul_of_nonneg_left (cltm_double_sum hL a R' hR0.le) (by positivity)
      _ ≤ x ^ 2 := by
          rw [← hlam2, hx]
          have h3 : (2 * R' + 1) ^ 2 ≤ (3 * R') ^ 2 := by nlinarith
          calc V ^ 2 * ((2 * R' + 1) ^ 2 * lam ^ 2) ≤ V ^ 2 * ((3 * R') ^ 2 * lam ^ 2) := by gcongr
            _ = (3 * V * R' * lam) ^ 2 := by ring
            _ ≤ (9 * V * R' * lam) ^ 2 := by
                have : 0 ≤ V * R' * lam := by positivity
                nlinarith [sq_nonneg (V * R' * lam)]
  calc ∑ β, z β * (∑ β' ∈ CltMoments.ball L R' β, z β') ^ (m + 1)
      = ∑ β, ((∑ β' ∈ CltMoments.ball L R' β, z β') ^ m) * (z β * ∑ β' ∈ CltMoments.ball L R' β, z β') := by
        refine Finset.sum_congr rfl fun β _ => by ring
    _ ≤ ∑ β, x ^ m * (z β * ∑ β' ∈ CltMoments.ball L R' β, z β') :=
        Finset.sum_le_sum fun β _ => mul_le_mul_of_nonneg_right (hpow β)
          (mul_nonneg (hz0 β) (hBnn β))
    _ = x ^ m * ∑ β, z β * ∑ β' ∈ CltMoments.ball L R' β, z β' := by rw [Finset.mul_sum]
    _ ≤ x ^ m * x ^ 2 := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = x ^ (m + 1 + 1) := by ring

/-- Case 2 cluster count. -/
private theorem cltm_clusterSum_case2 (hL : 3 ≤ L) (p : ℕ) (z : Z2 L → ℝ)
    (hz0 : ∀ β, 0 ≤ z β) (V : ℝ) (hV : 0 ≤ V) (a : Z2 L) (hz : ∀ β, z β ≤ V * cltFw a β)
    (R' : ℝ) (hR' : 1 ≤ R') :
    CltMoments.clusterSum L (2 * p) z R' ≤ ((2 * p : ℕ) : ℝ) ^ (2 * p) *
      (9 * V * R' * Real.sqrt (5 + 4 * Real.log L)) ^ (2 * p) := by
  set x : ℝ := 9 * V * R' * Real.sqrt (5 + 4 * Real.log L) with hx
  have hx0 : 0 ≤ x := by positivity
  refine cltm_clusterSum_le_of_bound z hz0 R' (fun k => x ^ (k + 1))
    (fun k hk => cltm_T2 hL z hz0 V hV a hz R' hR' k hk) (x ^ (2 * p)) (by positivity) ?_
  intro φ hφ
  have hsum := cltm_sum_assigned hφ
  rw [Finset.prod_pow_eq_pow_sum]
  refine le_of_eq (congrArg (x ^ ·) ?_)
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  omega

private theorem cltm_clusterSum_nonneg {n : ℕ} (z : Z2 L → ℝ) (hz0 : ∀ β, 0 ≤ z β) (R : ℝ) :
    0 ≤ CltMoments.clusterSum L n z R := by
  unfold CltMoments.clusterSum
  exact Finset.sum_nonneg fun φ _ => Finset.prod_nonneg fun s _ => Finset.sum_nonneg fun β _ =>
    mul_nonneg (hz0 β) (pow_nonneg (Finset.sum_nonneg fun β' _ => hz0 β') _)

end Combinatorics

/-- The tuple product of the centered field, `∏_{k<p}(Y_{b_k} - 𝔼Y_{b_k}) ∏_{k≥p}
conj(Y_{b_k} - 𝔼Y_{b_k})` (`clt-lemmamoment`), at the sample point `ω`. -/
def CltMoments.tuple {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {L : ℕ}
    (Y : Z2 L → Ω → ℂ) (p : ℕ) (b : Fin (2 * p) → Z2 L) (ω : Ω) : ℂ :=
  ∏ k : Fin (2 * p), (if (k : ℕ) < p then Y (b k) ω - ∫ ω', Y (b k) ω' ∂P
    else (starRingEnd ℂ) (Y (b k) ω - ∫ ω', Y (b k) ω' ∂P))

/-- `‖Y‖_max = max_b |Y_b|` at the sample point `ω`. -/
def CltMoments.ymax {Ω : Type*} {L : ℕ} [NeZero L] (Y : Z2 L → Ω → ℂ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun b => ‖Y b ω‖

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {L : ℕ} [NeZero L]

private theorem cltm_prod_split {M : Type*} [CommMonoid M] (p : ℕ) (A B : M) :
    ∏ k : Fin (2 * p), (if (k : ℕ) < p then A else B) = A ^ p * B ^ p := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < p then A else B) (2 * p), two_mul,
    Finset.prod_range_add]
  congr 1
  · rw [Finset.prod_congr rfl (g := fun _ => A) (fun i hi => by simp [Finset.mem_range.1 hi])]
    simp
  · rw [Finset.prod_congr rfl (g := fun _ => B) (fun i _ => by simp)]
    simp

variable {P}
variable {Y : Z2 L → Ω → ℂ} {B : ℝ}

private theorem cltm_Yt_meas (hYm : ∀ b, Measurable (Y b)) (b : Z2 L) :
    Measurable fun ω => Y b ω - ∫ ω', Y b ω' ∂P := (hYm b).sub measurable_const

private theorem cltm_int_norm_le (hYB : ∀ b ω, ‖Y b ω‖ ≤ B) (b : Z2 L) :
    ‖∫ ω', Y b ω' ∂P‖ ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := Y b) (C := B)
    (Filter.Eventually.of_forall fun ω => hYB b ω)
  simpa using this

private theorem cltm_tuple_meas (hYm : ∀ b, Measurable (Y b)) (p : ℕ) (b : Fin (2 * p) → Z2 L) :
    Measurable (CltMoments.tuple P Y p b) := by
  unfold CltMoments.tuple
  refine Finset.measurable_prod _ fun k _ => ?_
  by_cases hk : (k : ℕ) < p
  · simp only [hk, ite_true]; exact cltm_Yt_meas hYm _
  · simp only [hk, ite_false]
    exact Complex.continuous_conj.measurable.comp (cltm_Yt_meas hYm _)

private theorem cltm_factor_norm (p : ℕ) (b : Fin (2 * p) → Z2 L) (ω : Ω) (k : Fin (2 * p)) :
    ‖(if (k : ℕ) < p then Y (b k) ω - ∫ ω', Y (b k) ω' ∂P
      else (starRingEnd ℂ) (Y (b k) ω - ∫ ω', Y (b k) ω' ∂P))‖
      = ‖Y (b k) ω - ∫ ω', Y (b k) ω' ∂P‖ := by
  split_ifs
  · rfl
  · exact RCLike.norm_conj _

private theorem cltm_tuple_norm_le (p : ℕ) (b : Fin (2 * p) → Z2 L) (ω : Ω) (c : ℝ)
    (hc : ∀ k, ‖Y (b k) ω - ∫ ω', Y (b k) ω' ∂P‖ ≤ c) :
    ‖CltMoments.tuple P Y p b ω‖ ≤ c ^ (2 * p) := by
  unfold CltMoments.tuple
  rw [norm_prod]
  calc ∏ k : Fin (2 * p), ‖(if (k : ℕ) < p then Y (b k) ω - ∫ ω', Y (b k) ω' ∂P
      else (starRingEnd ℂ) (Y (b k) ω - ∫ ω', Y (b k) ω' ∂P))‖
      ≤ ∏ _k : Fin (2 * p), c :=
        Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => by
          rw [cltm_factor_norm]; exact hc k
    _ = c ^ (2 * p) := by simp

private theorem cltm_tuple_int (hYm : ∀ b, Measurable (Y b)) (hYB : ∀ b ω, ‖Y b ω‖ ≤ B)
    (p : ℕ) (b : Fin (2 * p) → Z2 L) : Integrable (CltMoments.tuple P Y p b) P := by
  refine Integrable.of_bound (cltm_tuple_meas hYm p b).aestronglyMeasurable ((B + B) ^ (2 * p))
    (Filter.Eventually.of_forall fun ω => cltm_tuple_norm_le p b ω _ fun k => ?_)
  calc ‖Y (b k) ω - ∫ ω', Y (b k) ω' ∂P‖ ≤ ‖Y (b k) ω‖ + ‖∫ ω', Y (b k) ω' ∂P‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hYB _ _) (cltm_int_norm_le hYB _)

private theorem cltm_expand (hYm : ∀ b, Measurable (Y b)) (hYB : ∀ b ω, ‖Y b ω‖ ≤ B)
    (Z : Z2 L → ℂ) (p : ℕ) :
    ∫ ω, ‖∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖ ^ (2 * p) ∂P ≤
      ∑ b : Fin (2 * p) → Z2 L, (∏ k, ‖Z (b k)‖) * ‖∫ ω, CltMoments.tuple P Y p b ω ∂P‖ := by
  classical
  set S : Ω → ℂ := fun ω => ∑ x, Z x * (Y x ω - ∫ ω', Y x ω' ∂P) with hS
  have h1 : ∀ ω, (((‖S ω‖ ^ (2 * p) : ℝ)) : ℂ) = ∑ b : Fin (2 * p) → Z2 L,
      (∏ k : Fin (2 * p), (if (k : ℕ) < p then Z (b k) else (starRingEnd ℂ) (Z (b k)))) *
        CltMoments.tuple P Y p b ω := by
    intro ω
    have hA : (((‖S ω‖ ^ (2 * p) : ℝ)) : ℂ) = ∏ k : Fin (2 * p),
        (if (k : ℕ) < p then S ω else (starRingEnd ℂ) (S ω)) := by
      rw [cltm_prod_split, ← mul_pow, Complex.mul_conj', pow_mul]
      push_cast
      rfl
    have hB : ∀ k : Fin (2 * p), (if (k : ℕ) < p then S ω else (starRingEnd ℂ) (S ω)) =
        ∑ x : Z2 L, (if (k : ℕ) < p then Z x else (starRingEnd ℂ) (Z x)) *
          (if (k : ℕ) < p then Y x ω - ∫ ω', Y x ω' ∂P
            else (starRingEnd ℂ) (Y x ω - ∫ ω', Y x ω' ∂P)) := by
      intro k
      by_cases hk : (k : ℕ) < p
      · simp [hk, hS]
      · simp [hk, hS, map_sum]
    rw [hA, Finset.prod_congr rfl fun k _ => hB k]
    rw [Finset.prod_univ_sum (fun _ : Fin (2 * p) => (Finset.univ : Finset (Z2 L)))
      (fun k x => (if (k : ℕ) < p then Z x else (starRingEnd ℂ) (Z x)) *
          (if (k : ℕ) < p then Y x ω - ∫ ω', Y x ω' ∂P
            else (starRingEnd ℂ) (Y x ω - ∫ ω', Y x ω' ∂P)))]
    rw [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.prod_mul_distrib]
    rfl
  have hint : ∀ b : Fin (2 * p) → Z2 L, Integrable (fun ω =>
      (∏ k : Fin (2 * p), (if (k : ℕ) < p then Z (b k) else (starRingEnd ℂ) (Z (b k)))) *
        CltMoments.tuple P Y p b ω) P :=
    fun b => (cltm_tuple_int hYm hYB p b).const_mul _
  have h2 : ((∫ ω, ‖S ω‖ ^ (2 * p) ∂P : ℝ) : ℂ) = ∑ b : Fin (2 * p) → Z2 L,
      (∏ k : Fin (2 * p), (if (k : ℕ) < p then Z (b k) else (starRingEnd ℂ) (Z (b k)))) *
        ∫ ω, CltMoments.tuple P Y p b ω ∂P := by
    rw [← integral_complex_ofReal]
    simp_rw [h1]
    rw [integral_finsetSum _ (fun b _ => hint b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
  have h3 : ∫ ω, ‖S ω‖ ^ (2 * p) ∂P = ‖((∫ ω, ‖S ω‖ ^ (2 * p) ∂P : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun ω => by positivity)]
  rw [h3, h2]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_prod]
  refine le_of_eq (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  split_ifs
  · rfl
  · exact RCLike.norm_conj _

private theorem cltMax_meas (hYm : ∀ b, Measurable (Y b)) : Measurable (CltMoments.ymax Y) := by
  have := Finset.measurable_sup' (s := (Finset.univ : Finset (Z2 L))) Finset.univ_nonempty
    (f := fun b ω => ‖Y b ω‖) fun b _ => (hYm b).norm
  convert this using 1
  ext ω
  simp [CltMoments.ymax, Finset.sup'_apply]

private theorem cltMax_nonneg (ω : Ω) : 0 ≤ CltMoments.ymax Y ω :=
  (norm_nonneg (Y 0 ω)).trans (Finset.le_sup' (fun b => ‖Y b ω‖) (Finset.mem_univ (0 : Z2 L)))

private theorem cltMax_le (hYB : ∀ b ω, ‖Y b ω‖ ≤ B) (ω : Ω) : CltMoments.ymax Y ω ≤ B :=
  Finset.sup'_le _ _ fun b _ => hYB b ω

private theorem cltMax_int_pow (hYm : ∀ b, Measurable (Y b)) (hYB : ∀ b ω, ‖Y b ω‖ ≤ B) (q : ℕ) :
    Integrable (fun ω => CltMoments.ymax Y ω ^ q) P := by
  refine Integrable.of_bound ((cltMax_meas hYm).pow_const q).aestronglyMeasurable (B ^ q)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg (cltMax_nonneg ω) _)]
  exact pow_le_pow_left₀ (cltMax_nonneg ω) (cltMax_le hYB ω) q

private theorem cltm_pow_add_le (x m : ℝ) (hx : 0 ≤ x) (hm : 0 ≤ m) (q : ℕ) :
    (x + m) ^ q ≤ 2 ^ q * (x ^ q + m ^ q) / 2 := by
  have h := (convexOn_pow (𝕜 := ℝ) q).2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hm)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have h2 : (x + m) ^ q = 2 ^ q * (1 / 2 * x + 1 / 2 * m) ^ q := by
    rw [← mul_pow]; congr 1; ring
  rw [h2]
  calc 2 ^ q * (1 / 2 * x + 1 / 2 * m) ^ q ≤ 2 ^ q * (1 / 2 * x ^ q + 1 / 2 * m ^ q) := by gcongr
    _ = 2 ^ q * (x ^ q + m ^ q) / 2 := by ring

private theorem cltm_tuple_le (hYm : ∀ b, Measurable (Y b)) (hYB : ∀ b ω, ‖Y b ω‖ ≤ B)
    (p : ℕ) (b : Fin (2 * p) → Z2 L) :
    ‖∫ ω, CltMoments.tuple P Y p b ω ∂P‖ ≤ 2 ^ (2 * p) * ∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P := by
  set m : ℝ := ∫ ω, CltMoments.ymax Y ω ∂P with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ω => cltMax_nonneg ω
  have hMint : Integrable (CltMoments.ymax Y) P := by
    simpa using cltMax_int_pow (P := P) hYm hYB 1
  have hYint : ∀ x, Integrable (fun ω => ‖Y x ω‖) P := fun x =>
    Integrable.of_bound (hYm x).norm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hYB x ω)
  have hint_le : ∀ x, ‖∫ ω', Y x ω' ∂P‖ ≤ m := fun x =>
    (norm_integral_le_integral_norm _).trans
      (integral_mono (hYint x) hMint fun ω =>
        Finset.le_sup' (fun b => ‖Y b ω‖) (Finset.mem_univ x))
  have hpt : ∀ ω, ‖CltMoments.tuple P Y p b ω‖ ≤ (CltMoments.ymax Y ω + m) ^ (2 * p) := by
    intro ω
    refine cltm_tuple_norm_le p b ω _ fun k => ?_
    calc ‖Y (b k) ω - ∫ ω', Y (b k) ω' ∂P‖
        ≤ ‖Y (b k) ω‖ + ‖∫ ω', Y (b k) ω' ∂P‖ := norm_sub_le _ _
      _ ≤ CltMoments.ymax Y ω + m := add_le_add
          (Finset.le_sup' (fun b => ‖Y b ω‖) (Finset.mem_univ (b k))) (hint_le _)
  have hsumint : Integrable (fun ω => (CltMoments.ymax Y ω + m) ^ (2 * p)) P := by
    refine Integrable.of_bound (((cltMax_meas hYm).add_const m).pow_const _).aestronglyMeasurable
      ((B + m) ^ (2 * p)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (add_nonneg (cltMax_nonneg ω) hm0) _)]
    exact pow_le_pow_left₀ (add_nonneg (cltMax_nonneg ω) hm0) (add_le_add_left (cltMax_le hYB ω) m) _
  have hjensen : m ^ (2 * p) ≤ ∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P := by
    have := (convexOn_pow (𝕜 := ℝ) (2 * p)).map_integral_le (μ := P) (f := CltMoments.ymax Y)
      (continuousOn_pow _) isClosed_Ici
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (cltMax_nonneg ω)) hMint
      (cltMax_int_pow hYm hYB _)
    simpa [hm] using this
  calc ‖∫ ω, CltMoments.tuple P Y p b ω ∂P‖ ≤ ∫ ω, ‖CltMoments.tuple P Y p b ω‖ ∂P :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (CltMoments.ymax Y ω + m) ^ (2 * p) ∂P :=
        integral_mono ((cltm_tuple_int hYm hYB p b).norm) hsumint hpt
    _ ≤ ∫ ω, 2 ^ (2 * p) * (CltMoments.ymax Y ω ^ (2 * p) + m ^ (2 * p)) / 2 ∂P :=
        integral_mono hsumint (by
          exact ((cltMax_int_pow hYm hYB _).add (integrable_const _)).const_mul _ |>.div_const _)
          fun ω => cltm_pow_add_le _ _ (cltMax_nonneg ω) hm0 _
    _ = 2 ^ (2 * p) * ((∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P) + m ^ (2 * p)) / 2 := by
        rw [integral_div, integral_const_mul, integral_add (cltMax_int_pow hYm hYB _)
          (integrable_const _)]
        simp
    _ ≤ 2 ^ (2 * p) * ∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P := by nlinarith [hjensen, pow_pos (two_pos : (0:ℝ) < 2) (2 * p)]

/-- **The `2p`-th moment bound** (`eq:cltmomentfinal`), deterministic given the far
decorrelation `hfar` (`clt-lemmafar`, with threshold `R`, error `εf`): for a bounded
measurable field `Y : Z_L² → Ω → ℂ` and a row `Z`,
`𝔼|Σ_b Z_b (Y_b - 𝔼Y_b)|^{2p} ≤ 2^{2p} · 𝔼‖Y‖_max^{2p} · 𝒞_p(|Z|, 3R) + εf (Σ_b |Z_b|)^{2p}`,
where `𝒞_p` is the cluster sum `CltMoments.clusterSum` over free-index structures `(𝒮, φ)`
(`j = |𝒮| ≤ p` free indices; every other index within `3R` of its free index).  The radius is
`3R` (a maximal `3R`-separated set of free indices), independent of `p`; the paper writes
`W^{3τ} ℓ_u` for `3R` with `R = W^{2τ} ℓ_u`, which needs `W^τ ≥ 3`.  The factor `2^{2p}` is the
centering (`(𝔼‖Y‖_max)^{2p} ≤ 𝔼‖Y‖_max^{2p}`).  `hfar` is only asked for the tuples that have an
isolated index (`R ≤ |b_i - b_k|_L` for all `k ≠ i`, some `i`). -/
theorem cltMomentBound (hYm : ∀ b, Measurable (Y b)) (hYB : ∀ b ω, ‖Y b ω‖ ≤ B)
    (p : ℕ) (R εf : ℝ) (hR : 0 ≤ R) (hεf : 0 ≤ εf) (Z : Z2 L → ℂ)
    (hfar : ∀ b : Fin (2 * p) → Z2 L,
      (∃ i, ∀ k, k ≠ i → R ≤ (zdist2 L (b i - b k) : ℝ)) →
      ‖∫ ω, CltMoments.tuple P Y p b ω ∂P‖ ≤ εf) :
    ∫ ω, ‖∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖ ^ (2 * p) ∂P ≤
      2 ^ (2 * p) * (∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P) *
          CltMoments.clusterSum L (2 * p) (fun β => ‖Z β‖) (3 * R) + εf * (∑ b, ‖Z b‖) ^ (2 * p) := by
  classical
  set Q : ℝ := 2 ^ (2 * p) * ∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg (by positivity) (integral_nonneg fun ω => by
    have := cltMax_nonneg (Y := Y) ω; positivity)
  set w : (Fin (2 * p) → Z2 L) → ℝ := fun b => ∏ k, ‖Z (b k)‖ with hw
  have hw0 : ∀ b, 0 ≤ w b := fun b => Finset.prod_nonneg fun k _ => norm_nonneg _
  let NF : (Fin (2 * p) → Z2 L) → Prop := fun b =>
    ∀ i, ∃ k, k ≠ i ∧ (zdist2 L (b i - b k) : ℝ) < R
  have hbd : ∀ b : Fin (2 * p) → Z2 L,
      ‖∫ ω, CltMoments.tuple P Y p b ω ∂P‖ ≤ εf + (if NF b then Q else 0) := by
    intro b
    by_cases hb : NF b
    · have hite : (if NF b then Q else 0) = Q := by simp [hb]
      rw [hite]
      have := cltm_tuple_le (P := P) hYm hYB p b
      linarith
    · have hite : (if NF b then Q else 0) = 0 := by simp [hb]
      rw [hite]
      refine le_trans (hfar b ?_) (by linarith)
      by_contra hcon
      apply hb
      intro i
      push Not at hcon
      exact hcon i
  have hsumw : ∑ b : Fin (2 * p) → Z2 L, w b = (∑ x : Z2 L, ‖Z x‖) ^ (2 * p) := by
    have := Finset.prod_univ_sum (fun _ : Fin (2 * p) => (Finset.univ : Finset (Z2 L)))
      (fun _ x => ‖Z x‖)
    rw [Fintype.piFinset_univ] at this
    rw [hw]; simp only
    rw [← this]
    simp
  calc ∫ ω, ‖∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖ ^ (2 * p) ∂P
      ≤ ∑ b : Fin (2 * p) → Z2 L, w b * ‖∫ ω, CltMoments.tuple P Y p b ω ∂P‖ := cltm_expand hYm hYB Z p
    _ ≤ ∑ b : Fin (2 * p) → Z2 L, w b * (εf + (if NF b then Q else 0)) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hbd b) (hw0 b)
    _ = εf * ∑ b : Fin (2 * p) → Z2 L, w b + Q * ∑ b ∈ Finset.univ.filter NF, w b := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> ring
    _ ≤ εf * (∑ x : Z2 L, ‖Z x‖) ^ (2 * p) + Q * CltMoments.clusterSum L (2 * p) (fun β => ‖Z β‖) (3 * R) := by
        rw [hsumw]
        gcongr
        exact cltm_nonfar_sum_le (fun β => ‖Z β‖) (fun β => norm_nonneg _) R hR
    _ = _ := by rw [hQ]; ring

private theorem cltm_even_pow_nonneg (x : ℝ) (p : ℕ) : 0 ≤ x ^ (2 * p) := by
  rw [pow_mul]; positivity

private theorem cltm_Emax_pow_le (hYm : ∀ b, Measurable (Y b)) (hYB : ∀ b ω, ‖Y b ω‖ ≤ B)
    (p : ℕ) (Λ' q₁ : ℝ) (hq₁ : 0 ≤ q₁)
    (hdom : ∀ b, P {ω | Λ' < ‖Y b ω‖} ≤ ENNReal.ofReal q₁) :
    ∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P ≤ Λ' ^ (2 * p) + B ^ (2 * p) * ((Fintype.card (Z2 L) : ℝ) * q₁) := by
  set bad : Set Ω := {ω | Λ' < CltMoments.ymax Y ω} with hbad
  have hbadm : MeasurableSet bad := measurableSet_lt measurable_const (cltMax_meas hYm)
  have hΛ0 : 0 ≤ Λ' ^ (2 * p) := cltm_even_pow_nonneg _ _
  have hpt : ∀ ω, CltMoments.ymax Y ω ^ (2 * p) ≤ Λ' ^ (2 * p) + bad.indicator (fun _ => B ^ (2 * p)) ω := by
    intro ω
    by_cases hω : ω ∈ bad
    · rw [Set.indicator_of_mem hω]
      have : CltMoments.ymax Y ω ^ (2 * p) ≤ B ^ (2 * p) :=
        pow_le_pow_left₀ (cltMax_nonneg ω) (cltMax_le hYB ω) _
      linarith
    · rw [Set.indicator_of_notMem hω]
      have hle : CltMoments.ymax Y ω ≤ Λ' := not_lt.1 hω
      have : CltMoments.ymax Y ω ^ (2 * p) ≤ Λ' ^ (2 * p) := pow_le_pow_left₀ (cltMax_nonneg ω) hle _
      linarith
  have hint2 : Integrable (fun ω => Λ' ^ (2 * p) + bad.indicator (fun _ => B ^ (2 * p)) ω) P :=
    (integrable_const _).add ((integrable_const _).indicator hbadm)
  have hbadP : P.real bad ≤ (Fintype.card (Z2 L) : ℝ) * q₁ := by
    have hsub : bad ⊆ ⋃ b : Z2 L, {ω | Λ' < ‖Y b ω‖} := by
      intro ω hω
      obtain ⟨b₀, _, hb₀⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset (Z2 L)).Nonempty)
        (fun b => ‖Y b ω‖)
      have : Λ' < CltMoments.ymax Y ω := hω
      rw [show CltMoments.ymax Y ω = ‖Y b₀ ω‖ from hb₀] at this
      exact Set.mem_iUnion.2 ⟨b₀, this⟩
    calc P.real bad ≤ P.real (⋃ b : Z2 L, {ω | Λ' < ‖Y b ω‖}) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ b : Z2 L, P.real {ω | Λ' < ‖Y b ω‖} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _b : Z2 L, q₁ := Finset.sum_le_sum fun b _ => by
          rw [measureReal_def]
          calc (P {ω | Λ' < ‖Y b ω‖}).toReal ≤ (ENNReal.ofReal q₁).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdom b)
            _ = q₁ := ENNReal.toReal_ofReal hq₁
      _ = (Fintype.card (Z2 L) : ℝ) * q₁ := by simp
  calc ∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P
      ≤ ∫ ω, (Λ' ^ (2 * p) + bad.indicator (fun _ => B ^ (2 * p)) ω) ∂P :=
        integral_mono (cltMax_int_pow hYm hYB _) hint2 hpt
    _ = Λ' ^ (2 * p) + P.real bad * B ^ (2 * p) := by
        rw [integral_add (integrable_const _) ((integrable_const _).indicator hbadm),
          integral_const, integral_indicator_const _ hbadm]
        simp
    _ ≤ Λ' ^ (2 * p) + ((Fintype.card (Z2 L) : ℝ) * q₁) * B ^ (2 * p) := by
        gcongr
        exact cltm_even_pow_nonneg _ _
    _ = Λ' ^ (2 * p) + B ^ (2 * p) * ((Fintype.card (Z2 L) : ℝ) * q₁) := by ring

private theorem cltm_S_meas (hYm : ∀ b, Measurable (Y b)) (Z : Z2 L → ℂ) :
    Measurable fun ω => ∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P) :=
  Finset.measurable_sum _ fun b _ => (cltm_Yt_meas hYm b).const_mul _

private theorem cltm_S_norm_le (hYB : ∀ b ω, ‖Y b ω‖ ≤ B) (Z : Z2 L → ℂ) (ω : Ω) :
    ‖∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖ ≤ (∑ b, ‖Z b‖) * (B + B) := by
  calc ‖∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖
      ≤ ∑ b, ‖Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖ := norm_sum_le _ _
    _ ≤ ∑ b, ‖Z b‖ * (B + B) := Finset.sum_le_sum fun b _ => by
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖Y b ω - ∫ ω', Y b ω' ∂P‖ ≤ ‖Y b ω‖ + ‖∫ ω', Y b ω' ∂P‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (hYB _ _) (cltm_int_norm_le hYB _)
    _ = (∑ b, ‖Z b‖) * (B + B) := by rw [Finset.sum_mul]

private theorem cltm_engine (hYm : ∀ b, Measurable (Y b)) (hYB : ∀ b ω, ‖Y b ω‖ ≤ B)
    (p : ℕ) (R εf : ℝ) (hR : 0 ≤ R) (hεf : 0 ≤ εf) (Z : Z2 L → ℂ)
    (hfar : ∀ b : Fin (2 * p) → Z2 L,
      (∃ i, ∀ k, k ≠ i → R ≤ (zdist2 L (b i - b k) : ℝ)) →
      ‖∫ ω, CltMoments.tuple P Y p b ω ∂P‖ ≤ εf)
    (Λ' q₁ : ℝ) (hq₁ : 0 ≤ q₁)
    (hdom : ∀ b, P {ω | Λ' < ‖Y b ω‖} ≤ ENNReal.ofReal q₁)
    (Cq Sz : ℝ) (hCq : CltMoments.clusterSum L (2 * p) (fun β => ‖Z β‖) (3 * R) ≤ Cq)
    (hSz : ∑ b, ‖Z b‖ ≤ Sz) (θ : ℝ) (hθ : 0 < θ) :
    P {ω | θ < ‖∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖} ≤
      ENNReal.ofReal ((2 ^ (2 * p) * (Λ' ^ (2 * p) + B ^ (2 * p) *
        ((Fintype.card (Z2 L) : ℝ) * q₁)) * Cq + εf * Sz ^ (2 * p)) / θ ^ (2 * p)) := by
  have hmom := cltMomentBound hYm hYB p R εf hR hεf Z hfar
  have hE := cltm_Emax_pow_le hYm hYB p Λ' q₁ hq₁ hdom
  have hC0 := cltm_clusterSum_nonneg (n := 2 * p) (fun β => ‖Z β‖) (fun β => norm_nonneg _) (3 * R)
  have hM0 : 0 ≤ ∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P :=
    integral_nonneg fun ω => cltm_even_pow_nonneg _ _
  have hSnn : 0 ≤ ∑ b, ‖Z b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have hint : Integrable (fun ω => |‖∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖| ^ (2 * p)) P := by
    simp only [abs_norm]
    refine Integrable.of_bound (((cltm_S_meas hYm Z).norm).pow_const _).aestronglyMeasurable
      (((∑ b, ‖Z b‖) * (B + B)) ^ (2 * p)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (cltm_S_norm_le hYB Z ω) _
  refine RBM.Gauss.meas_gt_le_of_moment P hθ hint ?_
  simp only [abs_norm]
  calc ∫ ω, ‖∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖ ^ (2 * p) ∂P
      ≤ 2 ^ (2 * p) * (∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P) *
          CltMoments.clusterSum L (2 * p) (fun β => ‖Z β‖) (3 * R) + εf * (∑ b, ‖Z b‖) ^ (2 * p) := hmom
    _ ≤ 2 ^ (2 * p) * (Λ' ^ (2 * p) + B ^ (2 * p) * ((Fintype.card (Z2 L) : ℝ) * q₁)) * Cq +
          εf * Sz ^ (2 * p) := by
        have hE0 : 0 ≤ 2 ^ (2 * p) * (Λ' ^ (2 * p) + B ^ (2 * p) * ((Fintype.card (Z2 L) : ℝ) * q₁)) :=
          mul_nonneg (by positivity) (add_nonneg (cltm_even_pow_nonneg _ _)
            (mul_nonneg (cltm_even_pow_nonneg _ _) (mul_nonneg (Nat.cast_nonneg _) hq₁)))
        have h1 : 2 ^ (2 * p) * (∫ ω, CltMoments.ymax Y ω ^ (2 * p) ∂P) ≤
            2 ^ (2 * p) * (Λ' ^ (2 * p) + B ^ (2 * p) * ((Fintype.card (Z2 L) : ℝ) * q₁)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
        have h2 : (∑ b, ‖Z b‖) ^ (2 * p) ≤ Sz ^ (2 * p) := pow_le_pow_left₀ hSnn hSz _
        have h3 := mul_le_mul h1 hCq hC0 hE0
        have h4 := mul_le_mul_of_nonneg_left h2 hεf
        linarith

end Moments

section Deterministic

/-! ### Measurability of the matrix inverse (private) -/

section MatrixMeasurable

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {Θ : Type*} [MeasurableSpace Θ]

private theorem cltm_measurable_matrix_inv_apply {M : Θ → Matrix ν ν ℂ} (hM : Measurable M)
    (i j : ν) : Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

private theorem cltm_measurable_inv_entries {A : Θ → Matrix ν ν ℂ}
    (hA : ∀ k l, Measurable fun ω => A ω k l) (k l : ν) :
    Measurable fun ω => (A ω)⁻¹ k l :=
  cltm_measurable_matrix_inv_apply
    (Measurable.of_eval fun a => Measurable.of_eval fun b => hA a b) k l

end MatrixMeasurable

section CltY

variable {L W K : ℕ} [NeZero L] [NeZero W]

private theorem cltm_gEntry_meas {Θ : Type*} [MeasurableSpace Θ]
    (M : Θ → Matrix (Idx L W) (Idx L W) ℂ) (hM : ∀ i j, Measurable fun ω => M ω i j)
    (E s : ℝ) (σ : Bool) (x y : Idx L W) :
    Measurable fun ω => gEntry L W E s (M ω) σ x y := by
  unfold gEntry
  refine cltm_measurable_inv_entries (A := fun ω =>
    M ω - (if σ then spectralZ E s else (starRingEnd ℂ) (spectralZ E s)) •
      (1 : Matrix (Idx L W) (Idx L W) ℂ)) (fun k l => ?_) x y
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  exact (hM k l).sub measurable_const

private theorem cltm_cltY_meas {Θ : Type*} [MeasurableSpace Θ] (F : LocalForm L W 1 K)
    (M : Θ → Matrix (Idx L W) (Idx L W) ℂ) (hM : ∀ i j, Measurable fun ω => M ω i j)
    (E s : ℝ) (b : Z2 L) : Measurable fun ω => cltY F E s (M ω) b := by
  unfold cltY LocalForm.eval
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun q _ => ?_
  refine Measurable.const_mul (Finset.measurable_prod _ fun i _ => ?_) _
  exact cltm_gEntry_meas M hM E s _ _ _

open scoped Matrix.Norms.L2Operator in
private theorem cltm_gEntry_le (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (hH : M.IsHermitian) (σ : Bool) (x y : Idx L W) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E s).im|) : ‖gEntry L W E s M σ x y‖ ≤ η⁻¹ := by
  have hz' : η ≤ |(if σ then spectralZ E s else (starRingEnd ℂ) (spectralZ E s)).im| := by
    cases σ
    · simpa using hz
    · simpa using hz
  have h1 := norm_green_le hH hη hz'
  have h2 := norm_matrix_entry_le_opNorm (green M (if σ then spectralZ E s
    else (starRingEnd ℂ) (spectralZ E s))) x y
  exact h2.trans h1

private theorem cltm_cltY_le (F : LocalForm L W 1 K) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (hH : M.IsHermitian) {η C : ℝ} (hη : 0 < η)
    (hz : η ≤ |(spectralZ E s).im|) (hC : ∀ b j q, ‖F.coef b j q‖ ≤ C)
    (hΘ : 1 ≤ 2 * (Fintype.card (Idx L W) : ℝ) ^ 2 * η⁻¹) (b : Z2 L) :
    ‖cltY F E s M b‖ ≤ (K + 1) * C * (2 * (Fintype.card (Idx L W) : ℝ) ^ 2 * η⁻¹) ^ K := by
  set N : ℝ := (Fintype.card (Idx L W) : ℝ) with hN
  set Θ : ℝ := 2 * N ^ 2 * η⁻¹ with hΘdef
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (fun _ => b) 0 (fun i => i.elim0))
  have hterm : ∀ j : Fin (K + 1), ‖∑ q : Fin j → Idx L W × Idx L W × Bool,
      F.coef (fun _ => b) j q * ∏ i : Fin j, gEntry L W E s M (q i).2.2 (q i).1 (q i).2.1‖
      ≤ C * Θ ^ (j : ℕ) := by
    intro j
    calc ‖∑ q : Fin j → Idx L W × Idx L W × Bool,
          F.coef (fun _ => b) j q * ∏ i : Fin j, gEntry L W E s M (q i).2.2 (q i).1 (q i).2.1‖
        ≤ ∑ q : Fin j → Idx L W × Idx L W × Bool, C * (η⁻¹) ^ (j : ℕ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
          rw [norm_mul, norm_prod]
          refine mul_le_mul (hC _ _ _) ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _) hC0
          calc ∏ i : Fin j, ‖gEntry L W E s M (q i).2.2 (q i).1 (q i).2.1‖
              ≤ ∏ _i : Fin j, η⁻¹ :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ =>
                  cltm_gEntry_le E s M hH _ _ _ hη hz
            _ = (η⁻¹) ^ (j : ℕ) := by simp
      _ = (Fintype.card (Fin j → Idx L W × Idx L W × Bool) : ℝ) * (C * (η⁻¹) ^ (j : ℕ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = C * Θ ^ (j : ℕ) := by
          have hcard : (Fintype.card (Fin j → Idx L W × Idx L W × Bool) : ℝ) = (2 * N ^ 2) ^ (j : ℕ) := by
            rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod (Idx L W) (Idx L W × Bool),
              Fintype.card_prod (Idx L W) Bool, Fintype.card_bool]
            push_cast
            rw [hN]; ring
          rw [hcard, hΘdef, mul_pow]; ring
  unfold cltY LocalForm.eval
  calc ‖∑ j : Fin (K + 1), ∑ q : Fin j → Idx L W × Idx L W × Bool,
        F.coef (fun _ => b) j q * ∏ i : Fin j, gEntry L W E s M (q i).2.2 (q i).1 (q i).2.1‖
      ≤ ∑ j : Fin (K + 1), C * Θ ^ (j : ℕ) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    _ ≤ ∑ _j : Fin (K + 1), C * Θ ^ K :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hΘ (by have := j.2; omega)) hC0
    _ = (K + 1) * C * Θ ^ K := by simp; ring

end CltY

end Deterministic

section Arith

private theorem cltm_arith (p : ℕ) (a Λ θ₀ q c₁ V G H Cq Sz Bd Q₂ εf : ℝ) (ha : 1 ≤ a)
    (hΛ : 0 ≤ Λ) (hθ₀ : 0 < θ₀) (hq : 0 ≤ q) (hc₁ : 0 ≤ c₁)
    (hSz0 : 0 ≤ Sz) (hQ₂ : 0 ≤ Q₂) (hεf : 0 ≤ εf)
    (hCq : Cq ≤ c₁ * q ^ (2 * p)) (h3 : q * Λ ≤ θ₀ * V) (h4 : q ≤ θ₀ * G) (h5 : Sz ≤ θ₀ * H) :
    (2 ^ (2 * p) * ((a * Λ) ^ (2 * p) + Bd ^ (2 * p) * Q₂) * Cq + εf * Sz ^ (2 * p)) /
        (a ^ 2 * θ₀) ^ (2 * p)
      ≤ 2 ^ (2 * p) * c₁ * (V / a) ^ (2 * p) +
        2 ^ (2 * p) * c₁ * (Bd ^ (2 * p) * Q₂ * G ^ (2 * p)) + εf * H ^ (2 * p) := by
  have ha0 : 0 < a := by linarith
  have hY : 0 < (a ^ 2 * θ₀) ^ (2 * p) := by positivity
  rw [div_le_iff₀ hY]
  have h2p : (0 : ℝ) ≤ 2 ^ (2 * p) := by positivity
  have hBd : 0 ≤ Bd ^ (2 * p) := cltm_even_pow_nonneg _ _
  have hYge : θ₀ ^ (2 * p) ≤ (a ^ 2 * θ₀) ^ (2 * p) := by
    refine pow_le_pow_left₀ hθ₀.le ?_ _
    nlinarith [mul_le_mul_of_nonneg_right (by nlinarith : (1 : ℝ) ≤ a ^ 2) hθ₀.le]
  -- Cq ≥ ? we only use the upper bound; nonnegativity of the pieces:
  have hq2 : q ^ (2 * p) ≤ (θ₀ * G) ^ (2 * p) := pow_le_pow_left₀ hq h4 _
  -- term A
  have hA : 2 ^ (2 * p) * (a * Λ) ^ (2 * p) * Cq ≤
      2 ^ (2 * p) * c₁ * (V / a) ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p) := by
    have e1 : (V / a) ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p) = (a * θ₀ * V) ^ (2 * p) := by
      rw [← mul_pow]; congr 1; field_simp
    have e2 : (a * Λ) ^ (2 * p) * q ^ (2 * p) = (a * (q * Λ)) ^ (2 * p) := by
      rw [← mul_pow]; congr 1; ring
    have h6 : (a * (q * Λ)) ^ (2 * p) ≤ (a * θ₀ * V) ^ (2 * p) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      nlinarith
    calc 2 ^ (2 * p) * (a * Λ) ^ (2 * p) * Cq
        ≤ 2 ^ (2 * p) * (a * Λ) ^ (2 * p) * (c₁ * q ^ (2 * p)) :=
          mul_le_mul_of_nonneg_left hCq (mul_nonneg h2p (cltm_even_pow_nonneg _ _))
      _ = 2 ^ (2 * p) * c₁ * ((a * Λ) ^ (2 * p) * q ^ (2 * p)) := by ring
      _ ≤ 2 ^ (2 * p) * c₁ * (a * θ₀ * V) ^ (2 * p) := by
          rw [e2]; exact mul_le_mul_of_nonneg_left h6 (mul_nonneg h2p hc₁)
      _ = 2 ^ (2 * p) * c₁ * (V / a) ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p) := by rw [mul_assoc (2 ^ (2 * p) * c₁), e1]
  -- term B
  have hB : 2 ^ (2 * p) * (Bd ^ (2 * p) * Q₂) * Cq ≤
      2 ^ (2 * p) * c₁ * (Bd ^ (2 * p) * Q₂ * G ^ (2 * p)) * (a ^ 2 * θ₀) ^ (2 * p) := by
    have hGY : q ^ (2 * p) ≤ G ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p) := by
      calc q ^ (2 * p) ≤ (θ₀ * G) ^ (2 * p) := hq2
        _ = G ^ (2 * p) * θ₀ ^ (2 * p) := by rw [mul_pow]; ring
        _ ≤ G ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p) :=
            mul_le_mul_of_nonneg_left hYge (cltm_even_pow_nonneg _ _)
    calc 2 ^ (2 * p) * (Bd ^ (2 * p) * Q₂) * Cq
        ≤ 2 ^ (2 * p) * (Bd ^ (2 * p) * Q₂) * (c₁ * q ^ (2 * p)) :=
          mul_le_mul_of_nonneg_left hCq (mul_nonneg h2p (mul_nonneg hBd hQ₂))
      _ ≤ 2 ^ (2 * p) * (Bd ^ (2 * p) * Q₂) * (c₁ * (G ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGY hc₁)
            (mul_nonneg h2p (mul_nonneg hBd hQ₂))
      _ = 2 ^ (2 * p) * c₁ * (Bd ^ (2 * p) * Q₂ * G ^ (2 * p)) * (a ^ 2 * θ₀) ^ (2 * p) := by ring
  -- term C
  have hC : εf * Sz ^ (2 * p) ≤ εf * H ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p) := by
    have : Sz ^ (2 * p) ≤ H ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p) := by
      calc Sz ^ (2 * p) ≤ (θ₀ * H) ^ (2 * p) := pow_le_pow_left₀ hSz0 h5 _
        _ = H ^ (2 * p) * θ₀ ^ (2 * p) := by rw [mul_pow]; ring
        _ ≤ H ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p) :=
            mul_le_mul_of_nonneg_left hYge (cltm_even_pow_nonneg _ _)
    calc εf * Sz ^ (2 * p) ≤ εf * (H ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p)) :=
          mul_le_mul_of_nonneg_left this hεf
      _ = εf * H ^ (2 * p) * (a ^ 2 * θ₀) ^ (2 * p) := by ring
  calc 2 ^ (2 * p) * ((a * Λ) ^ (2 * p) + Bd ^ (2 * p) * Q₂) * Cq + εf * Sz ^ (2 * p)
      = 2 ^ (2 * p) * (a * Λ) ^ (2 * p) * Cq + 2 ^ (2 * p) * (Bd ^ (2 * p) * Q₂) * Cq +
          εf * Sz ^ (2 * p) := by ring
    _ ≤ (2 ^ (2 * p) * c₁ * (V / a) ^ (2 * p) +
        2 ^ (2 * p) * c₁ * (Bd ^ (2 * p) * Q₂ * G ^ (2 * p)) + εf * H ^ (2 * p)) *
        (a ^ 2 * θ₀) ^ (2 * p) := by nlinarith [hA, hB, hC]

end Arith

section Step

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {L : ℕ} [NeZero L] {Y : Z2 L → Ω → ℂ} {B : ℝ}

/-- The Markov step with the parameter bookkeeping: the failure probability at threshold
`a² θ₀` is at most a three-term expression: the bulk of `‖Y‖_max`, its large-value part, and the
far-decorrelation error. -/
private theorem cltm_step (hYm : ∀ b, Measurable (Y b)) (hYB : ∀ b ω, ‖Y b ω‖ ≤ B)
    (p : ℕ) (R εf : ℝ) (hR : 0 ≤ R) (hεf : 0 ≤ εf) (Z : Z2 L → ℂ)
    (hfar : ∀ b : Fin (2 * p) → Z2 L,
      (∃ i, ∀ k, k ≠ i → R ≤ (zdist2 L (b i - b k) : ℝ)) →
      ‖∫ ω, CltMoments.tuple P Y p b ω ∂P‖ ≤ εf)
    (a Λ θ₀ q c₁ V G H q₁ Sz : ℝ) (ha : 1 ≤ a) (hΛ : 0 ≤ Λ) (hθ₀ : 0 < θ₀) (hq : 0 ≤ q)
    (hc₁ : 0 ≤ c₁) (hq₁ : 0 ≤ q₁)
    (hdom : ∀ b, P {ω | a * Λ < ‖Y b ω‖} ≤ ENNReal.ofReal q₁)
    (hCq : CltMoments.clusterSum L (2 * p) (fun β => ‖Z β‖) (3 * R) ≤ c₁ * q ^ (2 * p))
    (hSz : ∑ b, ‖Z b‖ ≤ Sz) (h3 : q * Λ ≤ θ₀ * V) (h4 : q ≤ θ₀ * G) (h5 : Sz ≤ θ₀ * H) :
    P {ω | a ^ 2 * θ₀ < ‖∑ b, Z b * (Y b ω - ∫ ω', Y b ω' ∂P)‖} ≤
      ENNReal.ofReal (2 ^ (2 * p) * c₁ * (V / a) ^ (2 * p) +
        2 ^ (2 * p) * c₁ * (B ^ (2 * p) * ((Fintype.card (Z2 L) : ℝ) * q₁) * G ^ (2 * p)) +
        εf * H ^ (2 * p)) := by
  have hSz0 : 0 ≤ Sz := (Finset.sum_nonneg fun b _ => norm_nonneg _).trans hSz
  have hθ : 0 < a ^ 2 * θ₀ := by positivity
  refine (cltm_engine hYm hYB p R εf hR hεf Z hfar (a * Λ) q₁ hq₁ hdom _ Sz hCq hSz _ hθ).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  exact cltm_arith p a Λ θ₀ q c₁ V G H (c₁ * q ^ (2 * p)) Sz B
    ((Fintype.card (Z2 L) : ℝ) * q₁) εf ha hΛ hθ₀ hq hc₁ hSz0
    (mul_nonneg (Nat.cast_nonneg _) hq₁) hεf le_rfl h3 h4 h5

end Step

section Small

private theorem cltm_rpow_pow (N : ℝ) (hN : 0 < N) (x : ℝ) (k : ℕ) :
    (N ^ x) ^ k = N ^ (x * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]

/-- The three terms are `O(N^{-(D'+1)})`. -/
private theorem cltm_small (p : ℕ) (N a c₁ v₀ g₀ Cst ε e D' D₁ v g h b : ℝ)
    (V G H Bd Nn εf : ℝ) (hN : 1 ≤ N) (ha : a = N ^ (ε / 2)) (hc₁ : 0 ≤ c₁) (hv₀ : 0 ≤ v₀)
    (hCst : 0 ≤ Cst)
    (hV0 : 0 ≤ V) (hV : V ≤ v₀ * N ^ v) (hG0 : 0 ≤ G) (hG : G ≤ g₀ * N ^ g)
    (hH0 : 0 ≤ H) (hH : H ≤ N ^ h) (hBd0 : 0 ≤ Bd) (hBd : Bd ≤ Cst * N ^ b)
    (hNn0 : 0 ≤ Nn) (hNn : Nn ≤ N) (hεf : εf ≤ N ^ (-e))
    (E1 : 2 * p * (v - ε / 2) ≤ -(D' + 1)) (E2 : 2 * p * b + 1 + 2 * p * g - D₁ ≤ -(D' + 1))
    (E3 : -e + 2 * p * h ≤ -(D' + 1)) :
    2 ^ (2 * p) * c₁ * (V / a) ^ (2 * p) +
        2 ^ (2 * p) * c₁ * (Bd ^ (2 * p) * (Nn * N ^ (-D₁)) * G ^ (2 * p)) + εf * H ^ (2 * p)
      ≤ (2 ^ (2 * p) * c₁ * v₀ ^ (2 * p) + 2 ^ (2 * p) * c₁ * (Cst ^ (2 * p) * g₀ ^ (2 * p)) + 1) *
        N ^ (-(D' + 1)) := by
  have hN0 : 0 < N := by linarith
  have hmono : ∀ x y : ℝ, x ≤ y → N ^ x ≤ N ^ y := fun x y hxy =>
    Real.rpow_le_rpow_of_exponent_le hN hxy
  have h2p : (0 : ℝ) ≤ 2 ^ (2 * p) := by positivity
  have hap : 0 < a := by rw [ha]; exact Real.rpow_pos_of_pos hN0 _
  -- term 1
  have T1 : (V / a) ^ (2 * p) ≤ v₀ ^ (2 * p) * N ^ (-(D' + 1)) := by
    have h1 : V / a ≤ v₀ * N ^ (v - ε / 2) := by
      rw [div_le_iff₀ hap, ha, mul_assoc, ← Real.rpow_add hN0]
      convert hV using 3; ring
    calc (V / a) ^ (2 * p) ≤ (v₀ * N ^ (v - ε / 2)) ^ (2 * p) :=
          pow_le_pow_left₀ (div_nonneg hV0 hap.le) h1 _
      _ = v₀ ^ (2 * p) * N ^ ((v - ε / 2) * ((2 * p : ℕ) : ℝ)) := by
          rw [mul_pow, cltm_rpow_pow N hN0]
      _ ≤ v₀ ^ (2 * p) * N ^ (-(D' + 1)) := by
          refine mul_le_mul_of_nonneg_left (hmono _ _ ?_) (pow_nonneg hv₀ _)
          push_cast; linarith
  -- term 2
  have T2 : Bd ^ (2 * p) * (Nn * N ^ (-D₁)) * G ^ (2 * p) ≤
      Cst ^ (2 * p) * g₀ ^ (2 * p) * N ^ (-(D' + 1)) := by
    have hB' : Bd ^ (2 * p) ≤ Cst ^ (2 * p) * N ^ (b * ((2 * p : ℕ) : ℝ)) := by
      calc Bd ^ (2 * p) ≤ (Cst * N ^ b) ^ (2 * p) := pow_le_pow_left₀ hBd0 hBd _
        _ = _ := by rw [mul_pow, cltm_rpow_pow N hN0]
    have hG' : G ^ (2 * p) ≤ g₀ ^ (2 * p) * N ^ (g * ((2 * p : ℕ) : ℝ)) := by
      calc G ^ (2 * p) ≤ (g₀ * N ^ g) ^ (2 * p) := pow_le_pow_left₀ hG0 hG _
        _ = _ := by rw [mul_pow, cltm_rpow_pow N hN0]
    have hNn' : Nn * N ^ (-D₁) ≤ N ^ (1 - D₁) := by
      calc Nn * N ^ (-D₁) ≤ N * N ^ (-D₁) :=
            mul_le_mul_of_nonneg_right hNn (Real.rpow_nonneg hN0.le _)
        _ = N ^ (1 - D₁) := by
            rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_one]
    have hprod : Bd ^ (2 * p) * (Nn * N ^ (-D₁)) * G ^ (2 * p) ≤
        (Cst ^ (2 * p) * N ^ (b * ((2 * p : ℕ) : ℝ))) * N ^ (1 - D₁) *
          (g₀ ^ (2 * p) * N ^ (g * ((2 * p : ℕ) : ℝ))) := by
      refine mul_le_mul (mul_le_mul hB' hNn' (mul_nonneg hNn0 (Real.rpow_nonneg hN0.le _))
        (by positivity)) hG' (cltm_even_pow_nonneg _ _) (by positivity)
    refine hprod.trans ?_
    have hexp : N ^ (b * ((2 * p : ℕ) : ℝ)) * N ^ (1 - D₁) * N ^ (g * ((2 * p : ℕ) : ℝ))
        ≤ N ^ (-(D' + 1)) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      refine hmono _ _ ?_
      push_cast; linarith
    calc (Cst ^ (2 * p) * N ^ (b * ((2 * p : ℕ) : ℝ))) * N ^ (1 - D₁) *
          (g₀ ^ (2 * p) * N ^ (g * ((2 * p : ℕ) : ℝ)))
        = Cst ^ (2 * p) * g₀ ^ (2 * p) *
            (N ^ (b * ((2 * p : ℕ) : ℝ)) * N ^ (1 - D₁) * N ^ (g * ((2 * p : ℕ) : ℝ))) := by ring
      _ ≤ Cst ^ (2 * p) * g₀ ^ (2 * p) * N ^ (-(D' + 1)) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (cltm_even_pow_nonneg _ _)
            (cltm_even_pow_nonneg _ _))
  -- term 3
  have T3 : εf * H ^ (2 * p) ≤ N ^ (-(D' + 1)) := by
    calc εf * H ^ (2 * p) ≤ N ^ (-e) * (N ^ h) ^ (2 * p) :=
          mul_le_mul hεf (pow_le_pow_left₀ hH0 hH _) (cltm_even_pow_nonneg _ _)
            (Real.rpow_nonneg hN0.le _)
      _ = N ^ (-e + h * ((2 * p : ℕ) : ℝ)) := by
          rw [cltm_rpow_pow N hN0, ← Real.rpow_add hN0]
      _ ≤ N ^ (-(D' + 1)) := hmono _ _ (by push_cast; linarith)
  have hc : 0 ≤ 2 ^ (2 * p) * c₁ := mul_nonneg h2p hc₁
  calc 2 ^ (2 * p) * c₁ * (V / a) ^ (2 * p) +
        2 ^ (2 * p) * c₁ * (Bd ^ (2 * p) * (Nn * N ^ (-D₁)) * G ^ (2 * p)) + εf * H ^ (2 * p)
      ≤ 2 ^ (2 * p) * c₁ * (v₀ ^ (2 * p) * N ^ (-(D' + 1))) +
        2 ^ (2 * p) * c₁ * (Cst ^ (2 * p) * g₀ ^ (2 * p) * N ^ (-(D' + 1))) +
        N ^ (-(D' + 1)) := by
        gcongr
    _ = _ := by ring

end Small

section SeqFacts

variable (d : Sizes)

private theorem cltm_size_facts (n : ℕ) :
    1 ≤ ((d.size n : ℕ) : ℝ) ∧ (d.W n : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧
    (d.L n : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧ (1 : ℝ) ≤ (d.W n : ℝ) ∧
    (Fintype.card (Z2 (d.L n)) : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
  have hW : 1 ≤ d.W n := d.W_pos n
  have hL : 3 ≤ d.L n := d.three_le_L n
  have hcard : (Fintype.card (Z2 (d.L n)) : ℝ) = (d.L n : ℝ) ^ 2 := by
    simp [Z2, Fintype.card_prod, ZMod.card, pow_two]
  have hsz : ((d.size n : ℕ) : ℝ) = ((d.W n : ℝ) * (d.L n : ℝ)) ^ 2 := by
    simp [Sizes.size]
  have hW' : (1 : ℝ) ≤ (d.W n : ℝ) := by exact_mod_cast hW
  have hL' : (3 : ℝ) ≤ (d.L n : ℝ) := by exact_mod_cast hL
  rw [hsz, hcard]
  set w : ℝ := (d.W n : ℝ)
  set l : ℝ := (d.L n : ℝ)
  have hwl : 3 ≤ w * l := by nlinarith
  have hsq : w * l ≤ (w * l) ^ 2 := by nlinarith
  refine ⟨by nlinarith, ?_, ?_, hW', ?_⟩
  · nlinarith
  · nlinarith
  · rw [mul_pow]
    have : 1 ≤ w ^ 2 := by nlinarith
    nlinarith [sq_nonneg l]

end SeqFacts


section SeqY

variable (d : Sizes)

/-- `c_κ = √(κ(4-κ))/2`, the lower bound `Im m^{(E)} ≥ c_κ` for `|E| ≤ 2 - κ` (private
re-derivation of `spectralM_im_ge` of `RBM2D/Loop/KBoundInner.lean`). -/
private def cltm_ck (κ : ℝ) : ℝ := Real.sqrt (κ * (4 - κ)) / 2

private theorem cltm_ck_le_im {κ E : ℝ} (hE : |E| ≤ 2 - κ) : cltm_ck κ ≤ (spectralM E).im := by
  rw [spectralM_im, cltm_ck]
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hE0 hE 2
  have : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

private theorem cltm_ck_pos {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : 0 < cltm_ck κ := by
  have h1 : κ ≤ 2 := by have := abs_nonneg E; linarith
  unfold cltm_ck
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

private theorem cltm_ck_le_one {κ : ℝ} : cltm_ck κ ≤ 1 := by
  unfold cltm_ck
  have h : κ * (4 - κ) ≤ 2 ^ 2 := by nlinarith [sq_nonneg (κ - 2)]
  have := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (by norm_num)] at this
  linarith

private theorem cltm_card_idx (n : ℕ) :
    (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) = ((d.size n : ℕ) : ℝ) := by
  have : Fintype.card (Idx (d.L n) (d.W n)) = d.size n := by
    simp [Idx, Z2, Sizes.size, ZMod.card, sq]
  rw [this]

/-- The deterministic bound `‖Y‖_max ≤ (K+1) N^{C'} (2N³/c_κ)^K` (proof of `clt-lemma`,
"`‖Y_s‖_max = O(W^C)`"). -/
private theorem cltm_Y_bound (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (n : ℕ) (E u t : ℝ)
    (hE : |E| ≤ 2 - κ) (hut : u ≤ t) (ht : t < 1)
    (hR : ((d.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t) (K : ℕ)
    (F : LocalForm (d.L n) (d.W n) 1 K) (C' : ℝ)
    (hcoef : ∀ b j q, ‖F.coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C')
    (ω : Sizes.SeqΩ d) (b : Z2 (d.L n)) :
    ‖cltY F E u (Sizes.seqHflow d n u ω) b‖ ≤
      ((K : ℝ) + 1) * ((d.size n : ℕ) : ℝ) ^ C' *
        (2 * ((d.size n : ℕ) : ℝ) ^ 3 / cltm_ck κ) ^ K := by
  obtain ⟨hN1, -⟩ := cltm_size_facts d n
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hck := cltm_ck_pos hκ hE
  have hck1 : cltm_ck κ ≤ 1 := cltm_ck_le_one
  set η : ℝ := cltm_ck κ / N with hη
  have hη0 : 0 < η := by positivity
  have hRe : cltm_ck κ ≤ (spectralM E).im := cltm_ck_le_im hE
  have him : η ≤ |(spectralZ E u).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (by linarith) (lt_of_lt_of_le hck hRe))]
    have h1 : N⁻¹ ≤ 1 - u := by
      have h2 : N ^ (-1 : ℝ) ≤ N ^ (-1 + δ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      rw [Real.rpow_neg_one] at h2
      linarith
    calc η = N⁻¹ * cltm_ck κ := by rw [hη]; ring
      _ ≤ (1 - u) * (spectralM E).im :=
          mul_le_mul h1 hRe hck.le (by linarith)
  have hΘ : 1 ≤ 2 * (Fintype.card (Idx (d.L n) (d.W n)) : ℝ) ^ 2 * η⁻¹ := by
    rw [cltm_card_idx, ← hN, hη, inv_div]
    have : 1 ≤ N / cltm_ck κ := by rw [le_div_iff₀ hck]; linarith
    nlinarith [sq_nonneg N]
  have := cltm_cltY_le F E u (Sizes.seqHflow d n u ω) (Sizes.seqHflow_isHermitian d n u ω) hη0 him
    (C := N ^ C') hcoef hΘ b
  rw [cltm_card_idx, ← hN, hη, inv_div] at this
  refine this.trans (le_of_eq ?_)
  congr 2
  ring

end SeqY


section CltFarDef

variable (d : Sizes)

/-- **The far decorrelation claim** (`clt-lemmafar`) for the field
`Y_b = cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b` at decay scale `τ`: for every
`p ≥ 1` and `D > 0`, eventually in `n`, for every `b : Fin (2p) → Z_L²` with **some** index `i`
with `min_{k ≠ i} |b_i - b_k|_L ≥ W^{2τ} ℓ_u`, the expectation of
`∏_{k<p}(Y_{b_k} - 𝔼Y_{b_k}) ∏_{k≥p} conj(Y_{b_k} - 𝔼Y_{b_k})` has modulus `≤ W^{-D}`.  (The
paper's constant `c_D` is absorbed by "eventually" and "every `D`".) -/
def CltFar {K : ℕ} (F : ∀ n, LocalForm (d.L n) (d.W n) 1 K) (E u : ℕ → ℝ) (τ : ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop,
    ∀ b : Fin (2 * p) → Z2 (d.L n),
      (∃ i, ∀ k, k ≠ i →
        (d.W n : ℝ) ^ (2 * τ) * ellT (d.L n) (u n) ≤ (zdist2 (d.L n) (b i - b k) : ℝ)) →
      ‖∫ ω, ∏ k : Fin (2 * p),
          (if (k : ℕ) < p
            then cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (b k) -
              ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') (b k) ∂(Sizes.seqP d)
            else (starRingEnd ℂ) (cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (b k) -
              ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') (b k) ∂(Sizes.seqP d)))
        ∂(Sizes.seqP d)‖ ≤ (d.W n : ℝ) ^ (-D)

/-- `Λ_n ≥ 0` eventually, from the domination of `Y` at `(ε, D) = (1, 1)`. -/
private theorem cltm_Lam_nonneg {K : ℕ} (F : ∀ n, LocalForm (d.L n) (d.W n) 1 K) (E u Λ : ℕ → ℝ)
    (hT : SizeTendsto d)
    (hΛ : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
      (fun n p ω => ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
      (fun n _ _ => Λ n)) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ Λ n := by
  have h1 := hΛ 1 one_pos 1 one_pos
  filter_upwards [h1, hT.eventually_ge_atTop 2] with n hn hN2
  by_contra hneg
  push Not at hneg
  have hset : {ω | ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * Λ n <
      ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (((), (0 : Z2 (d.L n))) :
        Unit × Z2 (d.L n)).2‖} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have : ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * Λ n < 0 :=
      mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (by linarith) _) hneg
    exact lt_of_lt_of_le this (norm_nonneg _)
  have hle := hn ((), 0)
  rw [hset, measure_univ] at hle
  have h2 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
    have := (ENNReal.one_le_ofReal).1 hle
    exact this
  rw [Real.rpow_neg_one] at h2
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have : ((d.size n : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hN2
  linarith

end CltFarDef


private theorem cltm_final_le (N Kc D' : ℝ) (hN : 1 ≤ N) (hK : Kc ≤ N) :
    Kc * N ^ (-(D' + 1)) ≤ N ^ (-D') := by
  have hN0 : 0 < N := by linarith
  calc Kc * N ^ (-(D' + 1)) ≤ N * N ^ (-(D' + 1)) :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hN0.le _)
    _ = N ^ (-D') := by
        have h1 : N * N ^ (-(D' + 1)) = N ^ (1 + -(D' + 1)) := by
          rw [Real.rpow_add hN0, Real.rpow_one]
        rw [h1]; congr 1; ring

section Case1

variable (d : Sizes)

private theorem cltm_Bd_eq (N ck C' : ℝ) (hN : 0 < N) (K : ℕ) :
    ((K : ℝ) + 1) * N ^ C' * (2 * N ^ 3 / ck) ^ K
      = ((K : ℝ) + 1) * (2 / ck) ^ K * N ^ (C' + 3 * (K : ℝ)) := by
  have h2 : (N ^ 3) ^ K = N ^ (3 * (K : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast]; push_cast; ring_nf
  have h1 : (2 * N ^ 3 / ck) ^ K = (2 / ck) ^ K * N ^ (3 * (K : ℝ)) := by
    have : 2 * N ^ 3 / ck = (2 / ck) * N ^ 3 := by ring
    rw [this, mul_pow, h2]
  rw [h1, Real.rpow_add hN]
  ring

/-- A choice of `p ≥ 1` with `p ε ≥ D' + 2`. -/
private theorem cltm_exists_p (ε D' : ℝ) (hε : 0 < ε) (hD' : 0 < D') :
    ∃ p : ℕ, 1 ≤ p ∧ D' + 2 ≤ p * ε := by
  refine ⟨⌈(D' + 2) / ε⌉₊, ?_, ?_⟩
  · have : 0 < (D' + 2) / ε := by positivity
    exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 this).ne'
  · have := Nat.le_ceil ((D' + 2) / ε)
    rwa [div_le_iff₀ hε] at this

/-- **Case 1 of the `clt-lemma`** (`clt-lemma-final-result`) from the far decorrelation:
`CltCase1Prec d κ 𝔠 δ C` (`Case3Defs.lean`) with `Step2LocalPT`, `Step2DecayPT`,
`GbEXPHypV3` replaced by `CltFar d F E u τ`, for every constant `C ≥ 4`.  The deterministic bound
`‖Y‖_max = O(N^{C'+3K})` is proved here (`cltm_Y_bound`, from the coefficient bound, `|G| ≤ η⁻¹`
and `RangeCond`), not taken as a hypothesis.  Conditional on `CltFar`. -/
theorem cltCase1_of_far (κ 𝔠 δ C : ℝ) (hC : 4 ≤ C) :
    0 < κ → 0 < 𝔠 → 0 < δ →
    ∀ (K : ℕ) (C' τ D : ℝ), 0 ≤ C' → 0 < τ → 0 < D →
    ∀ (E s₀ t₀ u t Λ : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) 1 K)
      (Z : ∀ n, Matrix (Z2 (d.L n)) (Z2 (d.L n)) ℂ),
      (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s₀ n) → (∀ n, s₀ n ≤ u n) → (∀ n, u n ≤ t₀ n) →
      (∀ n, u n ≤ t n) → (∀ n, t n < 1) → SizeTendsto d → Bandwidth d 𝔠 → RangeCond d δ t →
      CltFar d F E u τ →
      (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') →
      (∀ n, (F n).Local τ (u n)) →
      PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
        (fun n p ω => ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
        (fun n _ _ => Λ n) →
      (∀ n a b, ellT (d.L n) (t n) * (d.W n : ℝ) ^ τ ≤ (zdist2 (d.L n) (a - b) : ℝ) →
        Z n a b = 0) →
      PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
        (fun n p ω => ‖∑ b : Z2 (d.L n), Z n p.2 b *
          (cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
            ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') b ∂(Sizes.seqP d))‖)
        (fun n p _ => (Finset.univ.sup' Finset.univ_nonempty fun b => ‖Z n p.2 b‖) *
          ((d.W n : ℝ) ^ (C * τ) * ellT (d.L n) (t n) * ellT (d.L n) (u n) * Λ n +
            (d.W n : ℝ) ^ (-D))) := by
  intro hκ h𝔠 hδ K C' τ D hC' hτ hD E s₀ t₀ u t Λ F Z hE hs₀ hs₀u hut₀ hut ht1 hSz hBW hRange
    hFar hcoef hloc hΛ hsupp ε hε D' hD'
  obtain ⟨p, hp1, hpε⟩ := cltm_exists_p ε D' hε hD'
  set bexp : ℝ := C' + 3 * K with hb
  have hb0 : 0 ≤ bexp := by rw [hb]; positivity
  set g : ℝ := 4 * τ + 2 + D with hg
  set Cst : ℝ := ((K : ℝ) + 1) * (2 / cltm_ck κ) ^ K with hCst
  set c₁ : ℝ := ((2 * p : ℕ) : ℝ) ^ (2 * p) with hc₁
  set D₁ : ℝ := 2 * p * bexp + 1 + 2 * p * g + D' + 1 with hD₁
  set D₀ : ℝ := (2 * p * (1 + D) + D' + 1) / 𝔠 with hD₀
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hD₁pos : 0 < D₁ := by rw [hD₁]; have : 0 < g := by rw [hg]; linarith
                             positivity
  have hD₀pos : 0 < D₀ := by rw [hD₀]; positivity
  set Kc : ℝ := 2 ^ (2 * p) * c₁ * 81 ^ (2 * p) +
    2 ^ (2 * p) * c₁ * (Cst ^ (2 * p) * 81 ^ (2 * p)) + 1 with hKc
  have hev1 := hΛ (ε / 2) (half_pos hε) D₁ hD₁pos
  have hev2 := cltm_Lam_nonneg d F E u Λ hSz hΛ
  have hev3 := hFar p hp1 D₀ hD₀pos
  have hev6 := hSz.eventually_ge_atTop (max Kc 2)
  filter_upwards [hev1, hev2, hev3, hBW, hRange, hev6] with n h1 h2 h3 h4 h5 h6
  intro x
  obtain ⟨⟨⟩, a⟩ := x
  obtain ⟨hN1, hWN, hLN, hW1, hNnN⟩ := cltm_size_facts d n
  have hLpos : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hu0 : 0 ≤ u n := (hs₀ n).trans (hs₀u n)
  have hℓu1 : 1 ≤ ellT (d.L n) (u n) := one_le_ellT hLpos hu0 ((hut n).trans_lt (ht1 n))
  have hℓul : ellT (d.L n) (u n) ≤ ellT (d.L n) (t n) :=
    (ellT_mono_ratio hLpos hu0 (hut n) (ht1 n)).1
  have hℓtL : ellT (d.L n) (t n) ≤ (d.L n : ℝ) := (ellT_pos_le hLpos (ht1 n)).2
  have hℓtN : ellT (d.L n) (t n) ≤ ((d.size n : ℕ) : ℝ) := hℓtL.trans hLN
  have hℓuN : ellT (d.L n) (u n) ≤ ((d.size n : ℕ) : ℝ) := hℓul.trans hℓtN
  have hYm : ∀ b : Z2 (d.L n),
      Measurable (fun ω => cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b) := fun b =>
    cltm_cltY_meas (F n) (Sizes.seqHflow d n (u n))
      (fun i j => Sizes.measurable_seqHflow_entry d n (u n) i j) (E n) (u n) b
  have hYB : ∀ (b : Z2 (d.L n)) (ω : Sizes.SeqΩ d),
      ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b‖ ≤
        Cst * ((d.size n : ℕ) : ℝ) ^ bexp := by
    intro b' ω
    have := cltm_Y_bound d κ δ hκ hδ n (E n) (u n) (t n) (hE n) (hut n) (ht1 n) h5 K (F n) C'
      (hcoef n) ω b'
    rw [cltm_Bd_eq _ _ _ (by linarith)] at this
    exact this
  -- scales
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  set W : ℝ := (d.W n : ℝ) with hW
  set ℓt : ℝ := ellT (d.L n) (t n) with hℓt
  set ℓu : ℝ := ellT (d.L n) (u n) with hℓu
  set Nn : ℝ := (Fintype.card (Z2 (d.L n)) : ℝ) with hNn
  have hN0 : 0 < N := by linarith
  have hW0 : 0 < W := by linarith
  have hw1 : 1 ≤ W ^ τ := Real.one_le_rpow hW1 hτ.le
  have hwN : W ^ τ ≤ N ^ τ := Real.rpow_le_rpow hW0.le hWN hτ.le
  set w : ℝ := W ^ τ with hw
  have hw0 : 0 < w := by linarith
  have hℓt1 : 1 ≤ ℓt := hℓu1.trans hℓul
  have hΛ0 : 0 ≤ Λ n := h2
  -- the target event
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun β : Z2 (d.L n) => ‖Z n a β‖) with hM
  have hzM : ∀ β, ‖Z n a β‖ ≤ M := fun β =>
    Finset.le_sup' (fun β => ‖Z n a β‖) (Finset.mem_univ β)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hzM 0)
  change (Sizes.seqP d) {ω | N ^ ε * (M * (W ^ (C * τ) * ℓt * ℓu * Λ n + W ^ (-D))) <
      ‖∑ β : Z2 (d.L n), Z n a β * (cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) β -
        ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') β ∂(Sizes.seqP d))‖} ≤
    ENNReal.ofReal (N ^ (-D'))
  rcases hM0.eq_or_lt with hM00 | hMpos
  · have hzero : ∀ β, Z n a β = 0 := fun β => by
      have := hzM β
      rw [← hM00] at this
      exact norm_le_zero_iff.1 this
    have hempty : {ω | N ^ ε * (M * (W ^ (C * τ) * ℓt * ℓu * Λ n + W ^ (-D))) <
        ‖∑ β : Z2 (d.L n), Z n a β * (cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) β -
          ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') β ∂(Sizes.seqP d))‖} = ∅ := by
      ext ω
      simp only [hzero, zero_mul, Finset.sum_const_zero, norm_zero, ← hM00, mul_zero,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_rfl
    rw [hempty, measure_empty]
    exact zero_le
  · have hWD : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
    have hWWD : W ^ (-D) * W ^ D = 1 := by rw [← Real.rpow_add hW0]; simp
    have hWD0 : 0 < W ^ D := Real.rpow_pos_of_pos hW0 _
    have hℓℓΛ : 0 ≤ ℓt * ℓu * Λ n :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hΛ0
    have hw4 : w ^ 4 ≤ W ^ (C * τ) := by
      have h1 : W ^ (C * τ) = w ^ C := by
        rw [hw, ← Real.rpow_mul hW0.le, mul_comm]
      rw [h1]
      have h4 : w ^ (4 : ℕ) = w ^ ((4 : ℕ) : ℝ) := (Real.rpow_natCast w 4).symm
      rw [h4]
      exact Real.rpow_le_rpow_of_exponent_le hw1 (by simpa using hC)
    set base : ℝ := W ^ (C * τ) * ℓt * ℓu * Λ n + W ^ (-D) with hbase
    have hbase0 : 0 < base := by
      have : 0 ≤ W ^ (C * τ) * ℓt * ℓu * Λ n := by
        have := mul_nonneg (Real.rpow_nonneg hW0.le (C * τ)) hℓℓΛ
        calc 0 ≤ W ^ (C * τ) * (ℓt * ℓu * Λ n) := this
          _ = _ := by ring
      linarith
    have hbaseW : W ^ (-D) ≤ base := by
      have : 0 ≤ W ^ (C * τ) * ℓt * ℓu * Λ n := by
        have := mul_nonneg (Real.rpow_nonneg hW0.le (C * τ)) hℓℓΛ
        calc 0 ≤ W ^ (C * τ) * (ℓt * ℓu * Λ n) := this
          _ = _ := by ring
      linarith
    have hbW : 1 ≤ base * W ^ D := by
      calc (1 : ℝ) = W ^ (-D) * W ^ D := hWWD.symm
        _ ≤ base * W ^ D := mul_le_mul_of_nonneg_right hbaseW hWD0.le
    have hw4base : w ^ 4 * ℓt * ℓu * Λ n ≤ base := by
      calc w ^ 4 * ℓt * ℓu * Λ n = w ^ 4 * (ℓt * ℓu * Λ n) := by ring
        _ ≤ W ^ (C * τ) * (ℓt * ℓu * Λ n) := mul_le_mul_of_nonneg_right hw4 hℓℓΛ
        _ = W ^ (C * τ) * ℓt * ℓu * Λ n := by ring
        _ ≤ base := by rw [hbase]; linarith
    have hθ₀ : 0 < M * base := mul_pos hMpos hbase0
    set u₁ : ℝ := 81 * w ^ 4 * ℓt * ℓu with hu₁
    have hu₁0 : 0 < u₁ := by
      rw [hu₁]; have : 0 < ℓt := by linarith
      have : 0 < ℓu := by linarith
      positivity
    set G : ℝ := u₁ * W ^ D with hG
    set H : ℝ := Nn * W ^ D with hH
    set q : ℝ := M * u₁ with hq
    set R : ℝ := W ^ (2 * τ) * ℓu with hR
    have hW2τ : W ^ (2 * τ) = w ^ 2 := by
      rw [hw, mul_comm, Real.rpow_mul hW0.le, Real.rpow_two]
    have hR1 : 1 ≤ R := by
      rw [hR, hW2τ]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hw1) hℓu1
    have hR0 : 0 ≤ R := by linarith
    have hρ : 1 ≤ ℓt * w := one_le_mul_of_one_le_of_one_le hℓt1 hw1
    have hsupp' : ∀ β, ℓt * w ≤ (zdist2 (d.L n) (a - β) : ℝ) → ‖Z n a β‖ = 0 := fun β hβ => by
      rw [hsupp n a β hβ, norm_zero]
    have hu1 : (3 * (ℓt * w)) * (3 * (3 * R)) ≤ u₁ := by
      rw [hR, hW2τ, hu₁]
      have hw3 : w ^ 3 ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
      have hp : 0 ≤ ℓt * ℓu := mul_nonneg (by linarith) (by linarith)
      calc (3 * (ℓt * w)) * (3 * (3 * (w ^ 2 * ℓu))) = 27 * w ^ 3 * (ℓt * ℓu) := by ring
        _ ≤ 27 * w ^ 4 * (ℓt * ℓu) := by gcongr
        _ ≤ 81 * w ^ 4 * (ℓt * ℓu) := by gcongr; norm_num
        _ = 81 * w ^ 4 * ℓt * ℓu := by ring
    have hu2 : (3 * (3 * R)) ^ 2 ≤ u₁ := by
      rw [hR, hW2τ, hu₁]
      have : ℓu * ℓu ≤ ℓt * ℓu := mul_le_mul_of_nonneg_right hℓul (by linarith)
      calc (3 * (3 * (w ^ 2 * ℓu))) ^ 2 = 81 * w ^ 4 * (ℓu * ℓu) := by ring
        _ ≤ 81 * w ^ 4 * (ℓt * ℓu) := by gcongr
        _ = 81 * w ^ 4 * ℓt * ℓu := by ring
    have hz0 : ∀ β, 0 ≤ ‖Z n a β‖ := fun β => norm_nonneg _
    have hCq := cltm_clusterSum_case1 p (fun β => ‖Z n a β‖) hz0 M hzM a (ℓt * w) hρ hsupp'
      (3 * R) (by linarith) u₁ hu1 hu2
    have hSz' : ∑ β, ‖Z n a β‖ ≤ Nn * M := by
      calc ∑ β, ‖Z n a β‖ ≤ (Finset.univ : Finset (Z2 (d.L n))).card • M :=
            Finset.sum_le_card_nsmul _ _ _ fun β _ => hzM β
        _ = Nn * M := by rw [Finset.card_univ, nsmul_eq_mul]
    have h3' : q * Λ n ≤ (M * base) * 81 := by
      calc q * Λ n = 81 * M * (w ^ 4 * ℓt * ℓu * Λ n) := by rw [hq, hu₁]; ring
        _ ≤ 81 * M * base := mul_le_mul_of_nonneg_left hw4base (by positivity)
        _ = (M * base) * 81 := by ring
    have h4' : q ≤ (M * base) * G := by
      calc q = M * u₁ * 1 := by rw [hq]; ring
        _ ≤ M * u₁ * (base * W ^ D) := mul_le_mul_of_nonneg_left hbW (by positivity)
        _ = (M * base) * G := by rw [hG]; ring
    have h5' : Nn * M ≤ (M * base) * H := by
      have hNn0' : 0 ≤ Nn := Nat.cast_nonneg _
      calc Nn * M = Nn * M * 1 := by ring
        _ ≤ Nn * M * (base * W ^ D) := mul_le_mul_of_nonneg_left hbW (by positivity)
        _ = (M * base) * H := by rw [hH]; ring
    have hdom : ∀ β : Z2 (d.L n), (Sizes.seqP d) {ω | N ^ (ε / 2) * Λ n <
        ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) β‖} ≤ ENNReal.ofReal (N ^ (-D₁)) :=
      fun β => h1 ((), β)
    have hstep := cltm_step (P := Sizes.seqP d)
      (Y := fun β ω => cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) β)
      (B := Cst * N ^ bexp) hYm hYB p R (W ^ (-D₀)) hR0 (Real.rpow_nonneg hW0.le _) (Z n a) h3
      (N ^ (ε / 2)) (Λ n) (M * base) q c₁ 81 G H (N ^ (-D₁)) (Nn * M)
      (Real.one_le_rpow hN1 (by positivity)) hΛ0 hθ₀ (by rw [hq]; positivity)
      (by rw [hc₁]; positivity) (Real.rpow_nonneg hN0.le _) hdom hCq hSz' h3' h4' h5'
    have hNe : N ^ ε = (N ^ (ε / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    rw [hNe]
    refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
    have hck := cltm_ck_pos hκ (hE n)
    have hCst0 : 0 ≤ Cst := by
      rw [hCst]
      exact mul_nonneg (by positivity) (pow_nonneg (div_nonneg (by norm_num) hck.le) _)
    have hG0 : 0 ≤ G := by rw [hG]; exact mul_nonneg hu₁0.le hWD0.le
    have hNg : N ^ g = N ^ (τ * ((4 : ℕ) : ℝ)) * N * N * N ^ D := by
      rw [show g = τ * ((4 : ℕ) : ℝ) + 1 + 1 + D by rw [hg]; push_cast; ring,
        Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
    have hw4N : w ^ 4 ≤ N ^ (τ * ((4 : ℕ) : ℝ)) := by
      rw [← cltm_rpow_pow N hN0 τ 4]
      exact pow_le_pow_left₀ hw0.le hwN 4
    have hWDN : W ^ D ≤ N ^ D := Real.rpow_le_rpow hW0.le hWN hD.le
    have hGle : G ≤ 81 * N ^ g := by
      rw [hG, hu₁, hNg]
      have hℓt0 : 0 ≤ ℓt := by linarith
      have hℓu0 : 0 ≤ ℓu := by linarith
      calc 81 * w ^ 4 * ℓt * ℓu * W ^ D
          ≤ 81 * N ^ (τ * ((4 : ℕ) : ℝ)) * N * N * N ^ D := by
            gcongr
        _ = 81 * (N ^ (τ * ((4 : ℕ) : ℝ)) * N * N * N ^ D) := by ring
    have hHle : H ≤ N ^ (1 + D) := by
      rw [hH, Real.rpow_add hN0, Real.rpow_one]
      exact mul_le_mul hNnN hWDN hWD0.le hN0.le
    have hNn0 : 0 ≤ Nn := Nat.cast_nonneg _
    have hH0 : 0 ≤ H := mul_nonneg hNn0 hWD0.le
    have hεfle : W ^ (-D₀) ≤ N ^ (-(𝔠 * D₀)) := by
      have h6' : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
      calc W ^ (-D₀) ≤ (N ^ 𝔠) ^ (-D₀) :=
            Real.rpow_le_rpow_of_nonpos h6' h4 (by linarith)
        _ = N ^ (-(𝔠 * D₀)) := by
            rw [← Real.rpow_mul hN0.le]; congr 1; ring
    have h𝔠D₀ : 𝔠 * D₀ = 2 * p * (1 + D) + D' + 1 := by
      rw [hD₀]; field_simp
    have hsm := cltm_small p N (N ^ (ε / 2)) c₁ 81 81 Cst ε (𝔠 * D₀) D' D₁ 0 g (1 + D) bexp
      81 G H (Cst * N ^ bexp) Nn (W ^ (-D₀)) hN1 rfl (by rw [hc₁]; positivity) (by norm_num)
      hCst0 (by norm_num) (by rw [Real.rpow_zero]; norm_num) hG0 hGle hH0 hHle
      (mul_nonneg hCst0 (Real.rpow_nonneg hN0.le _)) le_rfl hNn0 hNnN hεfle
      (by linarith) (by rw [hD₁]; linarith) (by rw [h𝔠D₀]; linarith)
    refine hsm.trans ?_
    exact cltm_final_le N Kc D' hN1 ((le_max_left _ _).trans h6)

end Case1


section Case2

variable (d : Sizes)

/-- `√(5 + 4 log L_n) ≤ N^η` eventually, for every `η > 0` (the logarithm of `sum_inv_sq_le`). -/
private theorem cltm_sqrt_log_le (hT : SizeTendsto d) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Real.sqrt (5 + 4 * Real.log (d.L n)) ≤ ((d.size n : ℕ) : ℝ) ^ η := by
  have hs : Tendsto (fun n : ℕ => ((d.size n : ℕ) : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp hT
  filter_upwards [hs.eventually_ge_atTop (5 + 4 / η)] with n hn
  obtain ⟨hN1, -, hLN, -, -⟩ := cltm_size_facts d n
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  set s : ℝ := N ^ η with hs'
  have hN0 : 0 < N := by linarith
  have hL0 : (0 : ℝ) < d.L n := by
    have := d.three_le_L n
    exact_mod_cast (by omega : 0 < d.L n)
  have hlog : Real.log (d.L n) ≤ s / η :=
    (Real.log_le_log hL0 hLN).trans (Real.log_le_rpow_div hN0.le hη)
  have hs1 : 1 ≤ s := Real.one_le_rpow hN1 hη.le
  rw [Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  have h1 : 4 * Real.log (d.L n) ≤ 4 * (s / η) := by linarith
  have h2 : 5 + 4 * (s / η) ≤ s ^ 2 := by
    have : (5 + 4 / η) * s ≤ s * s := by nlinarith
    calc 5 + 4 * (s / η) ≤ 5 * s + 4 / η * s := by
          have : 4 * (s / η) = 4 / η * s := by ring
          rw [this]; nlinarith
      _ = (5 + 4 / η) * s := by ring
      _ ≤ s * s := this
      _ = s ^ 2 := by ring
  linarith

/-- **Case 2 of the `clt-lemma`** (`clt-lemma-final-result2`) from the far decorrelation:
`CltCase2Prec d κ 𝔠 δ C` (`Case3Defs.lean`) with `Step2LocalPT`, `Step2DecayPT`,
`GbEXPHypV3` replaced by `CltFar d F E u τ`, for every constant `C ≥ 2`.  The lattice sum
`Σ_{|β'-β|_L ≤ R'} (1 + |a-β'|_L)⁻¹ ≤ e (1 + R') √(5 + 4 log L)` is `RBM.Evol.expInvSum`.
Conditional on `CltFar`. -/
theorem cltCase2_of_far (κ 𝔠 δ C : ℝ) (hC : 2 ≤ C) :
    0 < κ → 0 < 𝔠 → 0 < δ →
    ∀ (K : ℕ) (C' τ D : ℝ), 0 ≤ C' → 0 < τ → 0 < D →
    ∀ (E s₀ t₀ u t Λ : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) 1 K)
      (Z : ∀ n, Matrix (Z2 (d.L n)) (Z2 (d.L n)) ℂ),
      (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s₀ n) → (∀ n, s₀ n ≤ u n) → (∀ n, u n ≤ t₀ n) →
      (∀ n, u n ≤ t n) → (∀ n, t n < 1) → SizeTendsto d → Bandwidth d 𝔠 → RangeCond d δ t →
      CltFar d F E u τ →
      (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') →
      (∀ n, (F n).Local τ (u n)) →
      PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
        (fun n p ω => ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
        (fun n _ _ => Λ n) →
      (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ a b : Z2 (d.L n),
        ‖Z n a b‖ ≤ ((d.size n : ℕ) : ℝ) ^ ε * ((zdist2 (d.L n) (a - b) : ℝ) + 1)⁻¹) →
      PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × Z2 (d.L n))
        (fun n p ω => ‖∑ b : Z2 (d.L n), Z n p.2 b *
          (cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b -
            ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') b ∂(Sizes.seqP d))‖)
        (fun n _ _ => (d.W n : ℝ) ^ (C * τ) * ellT (d.L n) (u n) * Λ n +
          (d.W n : ℝ) ^ (-D)) := by
  intro hκ h𝔠 hδ K C' τ D hC' hτ hD E s₀ t₀ u t Λ F Z hE hs₀ hs₀u hut₀ hut ht1 hSz hBW hRange
    hFar hcoef hloc hΛ hZ ε hε D' hD'
  obtain ⟨p₀, hp₀1, hp₀ε⟩ := cltm_exists_p ε D' hε hD'
  set p : ℕ := p₀ + 1 with hpdef
  have hp1 : 1 ≤ p := by omega
  have hpε : D' + 2 + ε ≤ p * ε := by
    have : (p : ℝ) * ε = p₀ * ε + ε := by rw [hpdef]; push_cast; ring
    linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  set εZ : ℝ := ε / (8 * p) with hεZ
  have hεZ0 : 0 < εZ := by positivity
  set bexp : ℝ := C' + 3 * K with hb
  have hb0 : 0 ≤ bexp := by rw [hb]; positivity
  set g : ℝ := 2 * εZ + 2 * τ + 1 + D with hg
  set h' : ℝ := εZ + 1 + D with hh
  set Cst : ℝ := ((K : ℝ) + 1) * (2 / cltm_ck κ) ^ K with hCst
  set c₁ : ℝ := ((2 * p : ℕ) : ℝ) ^ (2 * p) with hc₁
  set D₁ : ℝ := 2 * p * bexp + 1 + 2 * p * g + D' + 1 with hD₁
  set D₀ : ℝ := (2 * p * h' + D' + 1) / 𝔠 with hD₀
  have hg0 : 0 < g := by rw [hg]; positivity
  have hh0 : 0 < h' := by rw [hh]; positivity
  have hD₁pos : 0 < D₁ := by rw [hD₁]; positivity
  have hD₀pos : 0 < D₀ := by rw [hD₀]; positivity
  set Kc : ℝ := 2 ^ (2 * p) * c₁ * 27 ^ (2 * p) +
    2 ^ (2 * p) * c₁ * (Cst ^ (2 * p) * 27 ^ (2 * p)) + 1 with hKc
  have hev1 := hΛ (ε / 2) (half_pos hε) D₁ hD₁pos
  have hev2 := cltm_Lam_nonneg d F E u Λ hSz hΛ
  have hev3 := hFar p hp1 D₀ hD₀pos
  have hev4 := hZ εZ hεZ0
  have hev5 := cltm_sqrt_log_le d hSz εZ hεZ0
  have hev6 := hSz.eventually_ge_atTop (max Kc 2)
  filter_upwards [hev1, hev2, hev3, hBW, hRange, hev6, hev4, hev5] with n h1 h2 h3 h4 h5 h6 h7 h8
  intro x
  obtain ⟨⟨⟩, a⟩ := x
  obtain ⟨hN1, hWN, hLN, hW1, hNnN⟩ := cltm_size_facts d n
  have hLpos : 1 ≤ d.L n := by have := d.three_le_L n; omega
  have hu0 : 0 ≤ u n := (hs₀ n).trans (hs₀u n)
  have hℓu1 : 1 ≤ ellT (d.L n) (u n) := one_le_ellT hLpos hu0 ((hut n).trans_lt (ht1 n))
  have hℓuL : ellT (d.L n) (u n) ≤ (d.L n : ℝ) :=
    (ellT_pos_le hLpos ((hut n).trans_lt (ht1 n))).2
  have hℓuN : ellT (d.L n) (u n) ≤ ((d.size n : ℕ) : ℝ) := hℓuL.trans hLN
  have hYm : ∀ b : Z2 (d.L n),
      Measurable (fun ω => cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b) := fun b =>
    cltm_cltY_meas (F n) (Sizes.seqHflow d n (u n))
      (fun i j => Sizes.measurable_seqHflow_entry d n (u n) i j) (E n) (u n) b
  have hYB : ∀ (b : Z2 (d.L n)) (ω : Sizes.SeqΩ d),
      ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) b‖ ≤
        Cst * ((d.size n : ℕ) : ℝ) ^ bexp := by
    intro b' ω
    have := cltm_Y_bound d κ δ hκ hδ n (E n) (u n) (t n) (hE n) (hut n) (ht1 n) h5 K (F n) C'
      (hcoef n) ω b'
    rw [cltm_Bd_eq _ _ _ (by linarith)] at this
    exact this
  -- scales
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  set W : ℝ := (d.W n : ℝ) with hW
  set ℓu : ℝ := ellT (d.L n) (u n) with hℓu
  set Nn : ℝ := (Fintype.card (Z2 (d.L n)) : ℝ) with hNn
  have hN0 : 0 < N := by linarith
  have hW0 : 0 < W := by linarith
  have hw1 : 1 ≤ W ^ τ := Real.one_le_rpow hW1 hτ.le
  have hwN : W ^ τ ≤ N ^ τ := Real.rpow_le_rpow hW0.le hWN hτ.le
  set w : ℝ := W ^ τ with hw
  have hw0 : 0 < w := by linarith
  have hΛ0 : 0 ≤ Λ n := h2
  change (Sizes.seqP d) {ω | N ^ ε * (W ^ (C * τ) * ℓu * Λ n + W ^ (-D)) <
      ‖∑ β : Z2 (d.L n), Z n a β * (cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) β -
        ∫ ω', cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω') β ∂(Sizes.seqP d))‖} ≤
    ENNReal.ofReal (N ^ (-D'))
  have hWD : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hWWD : W ^ (-D) * W ^ D = 1 := by rw [← Real.rpow_add hW0]; simp
  have hWD0 : 0 < W ^ D := Real.rpow_pos_of_pos hW0 _
  have hℓΛ : 0 ≤ ℓu * Λ n := mul_nonneg (by linarith) hΛ0
  have hw2 : w ^ 2 ≤ W ^ (C * τ) := by
    have h1 : W ^ (C * τ) = w ^ C := by
      rw [hw, ← Real.rpow_mul hW0.le, mul_comm]
    rw [h1]
    have h4 : w ^ (2 : ℕ) = w ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast w 2).symm
    rw [h4]
    exact Real.rpow_le_rpow_of_exponent_le hw1 (by simpa using hC)
  have hnn0 : 0 ≤ W ^ (C * τ) * ℓu * Λ n := by
    have := mul_nonneg (Real.rpow_nonneg hW0.le (C * τ)) hℓΛ
    calc 0 ≤ W ^ (C * τ) * (ℓu * Λ n) := this
      _ = _ := by ring
  set base : ℝ := W ^ (C * τ) * ℓu * Λ n + W ^ (-D) with hbase
  have hbase0 : 0 < base := by linarith
  have hbaseW : W ^ (-D) ≤ base := by linarith
  have hbW : 1 ≤ base * W ^ D := by
    calc (1 : ℝ) = W ^ (-D) * W ^ D := hWWD.symm
      _ ≤ base * W ^ D := mul_le_mul_of_nonneg_right hbaseW hWD0.le
  have hw2base : w ^ 2 * ℓu * Λ n ≤ base := by
    calc w ^ 2 * ℓu * Λ n = w ^ 2 * (ℓu * Λ n) := by ring
      _ ≤ W ^ (C * τ) * (ℓu * Λ n) := mul_le_mul_of_nonneg_right hw2 hℓΛ
      _ = W ^ (C * τ) * ℓu * Λ n := by ring
      _ ≤ base := by rw [hbase]; linarith
  set lam : ℝ := Real.sqrt (5 + 4 * Real.log (d.L n)) with hlam
  have hlam0 : 0 ≤ lam := Real.sqrt_nonneg _
  set V' : ℝ := N ^ εZ with hV'
  have hV'0 : 0 < V' := Real.rpow_pos_of_pos hN0 _
  set R : ℝ := W ^ (2 * τ) * ℓu with hR
  have hW2τ : W ^ (2 * τ) = w ^ 2 := by
    rw [hw, mul_comm, Real.rpow_mul hW0.le, Real.rpow_two]
  have hR1 : 1 ≤ R := by
    rw [hR, hW2τ]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hw1) hℓu1
  have hR0 : 0 ≤ R := by linarith
  set q : ℝ := 9 * V' * (3 * R) * lam with hq
  have hz0 : ∀ β, 0 ≤ ‖Z n a β‖ := fun β => norm_nonneg _
  have hzf : ∀ β, ‖Z n a β‖ ≤ V' * cltFw a β := fun β => h7 a β
  have hCq := cltm_clusterSum_case2 (d.three_le_L n) p (fun β => ‖Z n a β‖) hz0 V' hV'0.le a hzf
    (3 * R) (by linarith)
  have hSz' : ∑ β, ‖Z n a β‖ ≤ V' * Nn := by
    calc ∑ β, ‖Z n a β‖ ≤ ∑ _β : Z2 (d.L n), V' :=
          Finset.sum_le_sum fun β _ => (hzf β).trans
            (mul_le_of_le_one_right hV'0.le (cltFw_le_one a β))
      _ = V' * Nn := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  set G : ℝ := q * W ^ D with hG
  set H : ℝ := (V' * Nn) * W ^ D with hH
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hθ₀ : 0 < base := hbase0
  have h3' : q * Λ n ≤ base * (27 * V' * lam) := by
    calc q * Λ n = (27 * V' * lam) * (w ^ 2 * ℓu * Λ n) := by
          rw [hq, hR, hW2τ]; ring
      _ ≤ (27 * V' * lam) * base := mul_le_mul_of_nonneg_left hw2base (by positivity)
      _ = base * (27 * V' * lam) := by ring
  have h4' : q ≤ base * G := by
    calc q = q * 1 := by ring
      _ ≤ q * (base * W ^ D) := mul_le_mul_of_nonneg_left hbW hq0
      _ = base * G := by rw [hG]; ring
  have h5' : V' * Nn ≤ base * H := by
    have hNn0' : 0 ≤ Nn := Nat.cast_nonneg _
    calc V' * Nn = V' * Nn * 1 := by ring
      _ ≤ V' * Nn * (base * W ^ D) := mul_le_mul_of_nonneg_left hbW (by positivity)
      _ = base * H := by rw [hH]; ring
  have hdom : ∀ β : Z2 (d.L n), (Sizes.seqP d) {ω | N ^ (ε / 2) * Λ n <
      ‖cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) β‖} ≤ ENNReal.ofReal (N ^ (-D₁)) :=
    fun β => h1 ((), β)
  have hstep := cltm_step (P := Sizes.seqP d)
    (Y := fun β ω => cltY (F n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) β)
    (B := Cst * N ^ bexp) hYm hYB p R (W ^ (-D₀)) hR0 (Real.rpow_nonneg hW0.le _) (Z n a) h3
    (N ^ (ε / 2)) (Λ n) base q c₁ (27 * V' * lam) G H (N ^ (-D₁)) (V' * Nn)
    (Real.one_le_rpow hN1 (by positivity)) hΛ0 hθ₀ hq0
    (by rw [hc₁]; positivity) (Real.rpow_nonneg hN0.le _) hdom hCq hSz' h3' h4' h5'
  have hNe : N ^ ε = (N ^ (ε / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  rw [hNe]
  refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
  have hck := cltm_ck_pos hκ (hE n)
  have hCst0 : 0 ≤ Cst := by
    rw [hCst]
    exact mul_nonneg (by positivity) (pow_nonneg (div_nonneg (by norm_num) hck.le) _)
  have hV'lam : V' * lam ≤ N ^ (εZ + εZ) := by
    rw [Real.rpow_add hN0]
    exact mul_le_mul_of_nonneg_left h8 hV'0.le
  have hV0 : 0 ≤ 27 * V' * lam := by positivity
  have hVle : 27 * V' * lam ≤ 27 * N ^ (2 * εZ) := by
    calc 27 * V' * lam = 27 * (V' * lam) := by ring
      _ ≤ 27 * N ^ (εZ + εZ) := by gcongr
      _ = 27 * N ^ (2 * εZ) := by rw [two_mul]
  have hG0 : 0 ≤ G := by rw [hG]; exact mul_nonneg hq0 hWD0.le
  have hNg : N ^ g = N ^ εZ * N ^ εZ * N ^ (τ * ((2 : ℕ) : ℝ)) * N * N ^ D := by
    rw [show g = εZ + εZ + τ * ((2 : ℕ) : ℝ) + 1 + D by rw [hg]; push_cast; ring,
      Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
  have hw2N : w ^ 2 ≤ N ^ (τ * ((2 : ℕ) : ℝ)) := by
    rw [← cltm_rpow_pow N hN0 τ 2]
    exact pow_le_pow_left₀ hw0.le hwN 2
  have hWDN : W ^ D ≤ N ^ D := Real.rpow_le_rpow hW0.le hWN hD.le
  have hGle : G ≤ 27 * N ^ g := by
    rw [hG, hq, hR, hW2τ, hNg]
    have hℓu0 : 0 ≤ ℓu := by linarith
    have hV'lam' : V' * lam ≤ N ^ εZ * N ^ εZ := by
      rw [← Real.rpow_add hN0]; exact hV'lam
    calc 9 * V' * (3 * (w ^ 2 * ℓu)) * lam * W ^ D
        = 27 * (V' * lam) * w ^ 2 * ℓu * W ^ D := by ring
      _ ≤ 27 * (N ^ εZ * N ^ εZ) * N ^ (τ * ((2 : ℕ) : ℝ)) * N * N ^ D := by
          gcongr
      _ = 27 * (N ^ εZ * N ^ εZ * N ^ (τ * ((2 : ℕ) : ℝ)) * N * N ^ D) := by ring
  have hHle : H ≤ N ^ h' := by
    rw [hH, hh, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
    have hNn0 : 0 ≤ Nn := Nat.cast_nonneg _
    calc V' * Nn * W ^ D ≤ N ^ εZ * N * N ^ D := by gcongr
      _ = N ^ εZ * N * N ^ D := rfl
  have hNn0 : 0 ≤ Nn := Nat.cast_nonneg _
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hεfle : W ^ (-D₀) ≤ N ^ (-(𝔠 * D₀)) := by
    have h6' : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
    calc W ^ (-D₀) ≤ (N ^ 𝔠) ^ (-D₀) :=
          Real.rpow_le_rpow_of_nonpos h6' h4 (by linarith)
      _ = N ^ (-(𝔠 * D₀)) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
  have h𝔠D₀ : 𝔠 * D₀ = 2 * p * h' + D' + 1 := by
    rw [hD₀]; field_simp
  have h4pεZ : 4 * (p : ℝ) * εZ = ε / 2 := by rw [hεZ]; field_simp; ring
  have hsm := cltm_small p N (N ^ (ε / 2)) c₁ 27 27 Cst ε (𝔠 * D₀) D' D₁ (2 * εZ) g h' bexp
    (27 * V' * lam) G H (Cst * N ^ bexp) Nn (W ^ (-D₀)) hN1 rfl (by rw [hc₁]; positivity)
    (by norm_num) hCst0 hV0 hVle hG0 hGle hH0 hHle
    (mul_nonneg hCst0 (Real.rpow_nonneg hN0.le _)) le_rfl hNn0 hNnN hεfle
    (by linarith [h4pεZ, hpε, hε]) (by rw [hD₁]; linarith) (by rw [h𝔠D₀]; linarith)
  refine hsm.trans ?_
  exact cltm_final_le N Kc D' hN1 ((le_max_left _ _).trans h6)

end Case2


end RBM.Evol
