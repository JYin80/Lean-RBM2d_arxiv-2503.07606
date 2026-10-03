/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.HierVocab
import RBM2D.Induction.Split
import RBM2D.Induction.PerTimeCalc

/-!
# `lem_decayLoop` at a single time and its two corollaries

The theorems `decayLoopAt : DecayLoopAt d κ c τ C₀ E u P`,
`decayLoopWindow : DecayLoopWindow d κ c τ E s t` and
`decayLoopFromML : DecayLoopFromML d κ c τ E t`; their statements are in `RBM2D.Induction.HierVocab`,
section 4.  Paper: arXiv:2503.07606, Section 5, `lem_decayLoop`, `res_decayLK`; the paper omits
the proof ("identical to that of Lemma 5.9 in [YY_25]").

## Proof of `decayLoopAt` (`k ≥ 2`; for `k = 1` the far set is empty)

Let `a` be far, `ℓ_u W^{τ'} ≤ maxDist a`, and `c = (c₀, c₁)` a pair of adjacent labels.

1. **Adjacent pair** (`DecayLoop_adjacent`): some `(a_m, a_{m+1})` has
   `maxDist a ≤ (k-1) |a_m - a_{m+1}|_L` (triangle inequality along the chain).
2. **Cut** (`DecayLoop_cut`, `DecayLoop_pair`): rotate the loop until this pair is the pair
   (first label, last label) and cut it into a one-`G` chain and a `(k-1)`-chain.  The
   Cauchy–Schwarz step `norm_sq_gloop_le_symIdx` of `Induction/Split.lean` gives
   `|𝓛_{σ,a}|² ≤ |𝓛_{(+,-),c}| · |symmetric (k-1)-loop|`, and the second factor is at most
   `η_u^{-2(k-1)}` by `norm_gloop_le_of_le_abs_im`.  No entry bound of `G` is used.
3. **The 2-loop at the far pair**: `|𝓛_{(+,-),c}| ≤ |𝒦_{(+,-),c}| + |(𝓛-𝒦)_{(+,-),c}|`.
   The `𝒦` part is `KcalDecay` at length `2` (`Kpm = Kcal` of the 2-loop,
   `DecayLoop_Kpm_eq`); the `𝓛-𝒦` part is the decay input at the single label pair `c`, with
   `exp(-√(|c₀-c₁|_L/ℓ_u)) ≤ W^{-Q}` eventually (`DecayLoop_exp_small`).
4. **`lkGen`**: `|𝓛-𝒦| ≤ |𝓛| + |𝒦|`, and `|𝒦_{σ,a}| ≤ W^{-(D'+1)}` is `KcalDecay` at length `k`.
5. **Exponents** (`DecayLoop_alg`): `η_u⁻¹ ≤ (2/κ) N`, `M_u ≥ κ/2` (`scaleM_etaT_of_range`,
   `κ/2 ≤ Im m`), `P ≤ N^{C₀}`, `N ≤ W^{1/c}` (`Bandwidth`), and the exponent
   `Q = 2D' + (2(k-1) + 1 + C₀)/c + 1`.
6. **Probability**: only the event `{ω : |(𝓛-𝒦)_{u,(+,-),c}| > N^{1} ζ_c}` of the decay input at
   the pair `c = c(σ,a)` occurs, so the pointwise implication of `perTimeCalc_of_imp` closes it.

The hypotheses `GbEXPHypV3` and `InitLocal` of the statement are not used: the argument uses
step 2 instead of the entry bound (`GijGEX`); the entries of `G` never enter.

`decayLoopWindow` and `decayLoopFromML` apply `decayLoopAt` at every section `u` with
`s ≤ u ≤ t` (`Green.perTime_timeIcc_of_forall_seq`, `Green.perSeq_of_perTime_timeIcc`), with
`P = (η_s/η_u)^4 ∈ [1, N^4]` (`C₀ = 4`) and `P ≡ 1` (`C₀ = 0`, `InitDecay`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Ind RBM.Evol
open scoped NNReal ENNReal

/-! ## 1. The loop bound at an adjacent far pair (deterministic) -/

/-- Rotating a loop by `j` positions does not change `gloop` (iterating `gloop_rotate`). -/
private theorem DecayLoop_gloop_rotate_iter {L W : ℕ} [NeZero L]
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {z : ℂ} :
    ∀ (j : ℕ) (σ : List Bool) (a : List (Z2 L)), σ.length = a.length →
      gloop L W H z ⟨σ.rotate j, a.rotate j⟩ = gloop L W H z ⟨σ, a⟩ := by
  intro j
  induction j with
  | zero => intro σ a _; simp
  | succ j ih =>
    intro σ a h
    cases σ with
    | nil =>
      have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst this; simp
    | cons s σ =>
      cases a with
      | nil => simp at h
      | cons b a =>
        have h' : σ.length = a.length := by simpa using h
        rw [List.rotate_cons_succ, List.rotate_cons_succ]
        rw [ih (σ ++ [s]) (a ++ [b]) (by simp [h'])]
        exact (gloop_rotate s b h').symm

/-- **The cut.**  For a loop of length `k ≥ 2` and `m + 1 < k`, with `s = σ_{m+1}`,
`b' = a_{m+1}`, `b = a_m`:
`|𝓛_{σ,a}|² ≤ η^{-2(k-1)} |gloop ⟨[s, !s], [b', b]⟩|`.  The loop is rotated by `m + 1` so that
`(a_{m+1}, a_m)` is (first label, last label), then cut into the one-`G` chain `G_{σ_{m+1}}` and the
`(k-1)`-chain; `norm_sq_gloop_le_symIdx` (Cauchy–Schwarz) and `norm_gloop_le_of_le_abs_im`
(operator norm bound of the symmetric `(k-1)`-loop) finish. -/
private theorem DecayLoop_cut {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) {k : ℕ} (hk : 2 ≤ k) (σl : List Bool) (al : List (Z2 L))
    (hσ : σl.length = k) (ha : al.length = k) (m : ℕ) (hm : m + 1 < k) :
    ∃ (s : Bool) (b' b : Z2 L), σl[m + 1]? = some s ∧ al[m + 1]? = some b' ∧ al[m]? = some b ∧
      ‖gloop L W H z ⟨σl, al⟩‖ ^ 2 ≤
        η⁻¹ ^ (2 * (k - 1)) * ‖gloop L W H z ⟨[s, !s], [b', b]⟩‖ := by
  have hlen : σl.length = al.length := by omega
  have hrot := DecayLoop_gloop_rotate_iter (H := H) (z := z) (m + 1) σl al hlen
  obtain ⟨σA, σB, aA, aB, b', b, hσeq, haeq, hσA, haA, hσB, haB⟩ :=
    exists_split_loopIdx (k₁ := 1) (k₂ := k - 1) (by omega) (by omega)
      (σ := σl.rotate (m + 1)) (a := al.rotate (m + 1)) (by simp [hσ]; omega) (by simp [ha]; omega)
  have haA0 : aA = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨s, hs⟩ : ∃ s, σA = [s] := by
    match σA, hσA with
    | [s], _ => exact ⟨s, rfl⟩
  subst haA0
  subst hs
  refine ⟨s, b', b, ?_, ?_, ?_, ?_⟩
  · have h1 : (σl.rotate (m + 1))[0]? = some s := by
      rw [hσeq]; simp
    rw [List.getElem?_rotate (by omega)] at h1
    have : (0 + (m + 1)) % σl.length = m + 1 := by
      rw [hσ]; simp only [zero_add]; exact Nat.mod_eq_of_lt hm
    rwa [this] at h1
  · have h1 : (al.rotate (m + 1))[0]? = some b' := by
      rw [haeq]; simp
    rw [List.getElem?_rotate (by omega)] at h1
    have : (0 + (m + 1)) % al.length = m + 1 := by
      rw [ha]; simp only [zero_add]; exact Nat.mod_eq_of_lt hm
    rwa [this] at h1
  · have h1 : (al.rotate (m + 1))[k - 1]? = some b := by
      have : (al.rotate (m + 1)).getLast? = some b := by
        rw [haeq, List.nil_append, List.singleton_append, ← List.cons_append, List.getLast?_concat]
      rwa [List.getLast?_eq_getElem?, List.length_rotate, ha] at this
    rw [List.getElem?_rotate (by omega)] at h1
    have : (k - 1 + (m + 1)) % al.length = m := by
      rw [ha]
      have : k - 1 + (m + 1) = m + k := by omega
      rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rwa [this] at h1
  · rw [← hrot, hσeq, haeq]
    have h := norm_sq_gloop_le_symIdx (z := z) hH (σA := [s]) (σB := σB) (aA := []) (aB := aB)
      (by simp) (by omega) b' b
    refine h.trans ?_
    have hsym : symIdx [s] ([] : List (Z2 L)) b' b = ⟨[s, !s], [b', b]⟩ := by
      simp [symIdx]
    rw [hsym, mul_comm (η⁻¹ ^ (2 * (k - 1)))]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hB := norm_gloop_le_of_le_abs_im (z := z) (W := W) hH hη hz (symIdx σB aB b b')
      (by simp; omega) (by simp; omega)
    refine hB.trans ?_
    simp only [symIdx_a_length]
    have h2 : 2 * (aB.length + 1) = 2 * (k - 1) := by omega
    rw [h2]
    have hW : ((W : ℝ)⁻¹ ^ 2) ≤ 1 := by
      have : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
      have h3 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      have h4 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
      nlinarith
    have hW' : ((W : ℝ)⁻¹ ^ 2) ^ (2 * (k - 1) - 1) ≤ 1 :=
      pow_le_one₀ (by positivity) hW
    calc η⁻¹ ^ (2 * (k - 1)) * ((W : ℝ)⁻¹ ^ 2) ^ (2 * (k - 1) - 1)
        ≤ η⁻¹ ^ (2 * (k - 1)) * 1 := by gcongr
      _ = _ := mul_one _

/-! ### The adjacent pair with the largest gap -/

/-- `|-x|_L = |x|_L` on `Z_L`. -/
private theorem DecayLoop_zdist_neg {L : ℕ} [NeZero L] (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

/-- `|a - b|_L = |b - a|_L` on `Z_L²`. -/
private theorem DecayLoop_zdist2_comm {L : ℕ} [NeZero L] (a b : Z2 L) :
    zdist2 L (a - b) = zdist2 L (b - a) := by
  rw [← neg_sub b a]
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, DecayLoop_zdist_neg]

/-- The triangle inequality for `zdist2`. -/
private theorem DecayLoop_zdist2_tri {L : ℕ} [NeZero L] (a b c : Z2 L) :
    zdist2 L (a - c) ≤ zdist2 L (a - b) + zdist2 L (b - c) := by
  have := zdist2_add_le L (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

/-- **Some adjacent pair is far.**  `maxDist a ≤ (k-1) |a_m - a_{m+1}|_L` for some `m + 1 < k`
(triangle inequality along the chain `a_i, a_{i+1}, …, a_j`, which has at most `k - 1` steps). -/
private theorem DecayLoop_adjacent {L : ℕ} [NeZero L] {k : ℕ} (hk : 2 ≤ k) (a : Fin k → Z2 L) :
    ∃ (m : ℕ) (h : m + 1 < k),
      KLoop.maxDist L a ≤ (k - 1) * zdist2 L (a ⟨m, by omega⟩ - a ⟨m + 1, h⟩) := by
  classical
  let a' : ℕ → Z2 L := fun i => if h : i < k then a ⟨i, h⟩ else 0
  have ha' : ∀ i (h : i < k), a' i = a ⟨i, h⟩ := fun i h => by simp [a', h]
  let δ : ℕ → ℕ := fun i => zdist2 L (a' i - a' (i + 1))
  have hne : (Finset.range (k - 1)).Nonempty := ⟨0, by simp; omega⟩
  obtain ⟨m, hm, hΔ⟩ := Finset.exists_mem_eq_sup (Finset.range (k - 1)) hne δ
  have hm' : m + 1 < k := by have := Finset.mem_range.mp hm; omega
  refine ⟨m, hm', ?_⟩
  set Δ := (Finset.range (k - 1)).sup δ with hΔdef
  have hδΔ : ∀ i, i + 1 < k → δ i ≤ Δ := fun i hi =>
    Finset.le_sup (f := δ) (Finset.mem_range.mpr (by omega))
  have hchain : ∀ d i, i + d < k → zdist2 L (a' i - a' (i + d)) ≤ d * Δ := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hδΔ (i + d) (by omega)
      have h3 := DecayLoop_zdist2_tri (a' i) (a' (i + d)) (a' (i + (d + 1)))
      have h4 : δ (i + d) = zdist2 L (a' (i + d) - a' (i + (d + 1))) := by
        simp only [δ]; rfl
      rw [h4] at h2
      calc zdist2 L (a' i - a' (i + (d + 1)))
          ≤ zdist2 L (a' i - a' (i + d)) + zdist2 L (a' (i + d) - a' (i + (d + 1))) := h3
        _ ≤ d * Δ + Δ := by omega
        _ = (d + 1) * Δ := by ring
  have hmax : KLoop.maxDist L a ≤ (k - 1) * Δ := by
    unfold KLoop.maxDist
    refine Finset.sup_le fun p _ => ?_
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
    simp only
    rcases le_total i j with hij | hij
    · have := hchain (j - i) i (by omega)
      rw [show i + (j - i) = j by omega, ha' i hi, ha' j hj] at this
      calc _ ≤ (j - i) * Δ := this
        _ ≤ (k - 1) * Δ := Nat.mul_le_mul_right _ (by omega)
    · have := hchain (i - j) j (by omega)
      rw [show j + (i - j) = i by omega, ha' i hi, ha' j hj] at this
      rw [DecayLoop_zdist2_comm]
      calc _ ≤ (i - j) * Δ := this
        _ ≤ (k - 1) * Δ := Nat.mul_le_mul_right _ (by omega)
  have hmm : Δ = zdist2 L (a ⟨m, by omega⟩ - a ⟨m + 1, hm'⟩) := by
    rw [hΔ]
    simp only [δ]
    rw [ha' m (by omega), ha' (m + 1) hm']
  rw [← hmm]
  exact hmax

/-- `gloop ⟨[s, !s], [b', b]⟩` is the `(+,-)` two-loop at `(b', b)` (`s = +`) or at `(b, b')`
(`s = -`, by one rotation). -/
private theorem DecayLoop_gloop_two_sign {L W : ℕ} [NeZero L]
    {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {z : ℂ} (s : Bool) (b' b : Z2 L) :
    gloop L W H z ⟨[s, !s], [b', b]⟩ =
      gloop L W H z ⟨[true, false], [if s then b' else b, if s then b else b']⟩ := by
  cases s
  · have := gloop_rotate (L := L) (W := W) (H := H) (z := z) false b' (σ := [true]) (a := [b]) rfl
    simpa using this
  · simp

/-- **The far pair and the loop bound, with the pair independent of the matrix.**  For `k ≥ 2` there
is `c = (c₀, c₁)` (a function of `σ`, `a` only) with `maxDist a ≤ (k-1) |c₀ - c₁|_L` and, for
every Hermitian `H` and `η ≤ |Im z|`, `|𝓛_{σ,a}|² ≤ η^{-2(k-1)} |𝓛_{(+,-),c}|`. -/
private theorem DecayLoop_pair {L W : ℕ} [NeZero L] [NeZero W] {k : ℕ} (hk : 2 ≤ k)
    (σ : Fin k → Bool) (a : Fin k → Z2 L) :
    ∃ c : Z2 L × Z2 L,
      ((KLoop.maxDist L a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdist2 L (c.1 - c.2) : ℝ) ∧
      ∀ (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (η : ℝ), H.IsHermitian →
        0 < η → η ≤ |z.im| →
        ‖gloop L W H z (loopOf σ a)‖ ^ 2 ≤
          η⁻¹ ^ (2 * (k - 1)) * ‖gloop L W H z ⟨[true, false], [c.1, c.2]⟩‖ := by
  obtain ⟨m, hm, hmax⟩ := DecayLoop_adjacent hk a
  obtain ⟨s, hs⟩ : ∃ s : Bool, s = σ ⟨m + 1, hm⟩ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : Z2 L, b' = a ⟨m + 1, hm⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Z2 L, b = a ⟨m, by omega⟩ := ⟨_, rfl⟩
  refine ⟨(if s then b' else b, if s then b else b'), ?_, ?_⟩
  · have hcast : ((KLoop.maxDist L a : ℕ) : ℝ) ≤
        (((k - 1 : ℕ) : ℝ)) * (zdist2 L (b - b') : ℝ) := by
      rw [hb, hb']
      exact_mod_cast hmax
    have hk1 : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hk1] at hcast
    cases s
    · simpa using hcast
    · simp only [ite_true]
      rw [DecayLoop_zdist2_comm]
      simpa using hcast
  · intro H z η hH hη hz
    obtain ⟨s', b'', b''', hs', hb'', hb''', hbound⟩ := DecayLoop_cut (W := W) hH hη hz hk
      (List.ofFn σ) (List.ofFn a) (by simp) (by simp) m hm
    rw [List.getElem?_ofFn] at hs' hb'' hb'''
    simp only [hm, dite_true, show m < k by omega] at hs' hb'' hb'''
    have e1 : s' = s := by rw [hs]; exact (Option.some.inj hs').symm
    have e2 : b'' = b' := by rw [hb']; exact (Option.some.inj hb'').symm
    have e3 : b''' = b := by rw [hb]; exact (Option.some.inj hb''').symm
    rw [e1, e2, e3, DecayLoop_gloop_two_sign] at hbound
    exact hbound

/-! ## 2. The exponent bookkeeping (real numbers) -/

/-- **The chain of inequalities** for a far loop, in abstract real quantities: `Λ = |𝓛_{σ,a}|`,
`Lp = |𝓛_{(+,-),c}|`, `Kp = |𝒦_{(+,-),c}|`, `X = |(𝓛-𝒦)_{(+,-),c}|` bounded through the decay input
(`Pn` the prefactor, `Mi = M_u^{-2}`, `ex = exp(-√(|c₀-c₁|_L/ℓ_u))`), `Kc = |𝒦_{σ,a}|`, `ηi = η_u⁻¹`;
with `Q = 2D' + A(2(k-1) + 1 + C₀) + 1`, `A = 1/c` and `N ≤ W^A`, then `2Λ + Kc ≤ W^{-D'}` once
`W ≥ max(2, 16 Γ^{2(k-1)}(2 + Γ²))`. -/
private theorem DecayLoop_alg {W N Γ A ηi Λ Kp X Kc Lp Pn Mi ex : ℝ} {k : ℕ} {D' C₀ Q : ℝ}
    (hk : 2 ≤ k) (hC₀ : 0 ≤ C₀) (hΓ : 0 ≤ Γ)
    (hW : 2 ≤ W) (hWmin : 16 * Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2) ≤ W)
    (hN1 : 1 ≤ N) (hNW : N ≤ W ^ A)
    (hQ : Q = 2 * D' + A * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1)
    (hηi0 : 0 ≤ ηi) (hηi : ηi ≤ Γ * N)
    (hΛ0 : 0 ≤ Λ) (hLp0 : 0 ≤ Lp) (hΛ : Λ ^ 2 ≤ ηi ^ (2 * (k - 1)) * Lp)
    (hLp : Lp ≤ Kp + X) (hKp : Kp ≤ W ^ (-Q))
    (hX : X ≤ N * (Pn * Mi * ex + W ^ (-Q)))
    (hPn : Pn ≤ N ^ C₀) (hMi : Mi ≤ Γ ^ 2) (hex : ex ≤ W ^ (-Q))
    (hMi0 : 0 ≤ Mi) (hex0 : 0 ≤ ex)
    (hKc : Kc ≤ W ^ (-(D' + 1))) :
    2 * Λ + Kc ≤ W ^ (-D') := by
  have hW0 : 0 < W := by linarith
  have hWQ : 0 < W ^ (-Q) := Real.rpow_pos_of_pos hW0 _
  have hN0 : 0 < N := by linarith
  set r : ℝ := 2 * ((k : ℝ) - 1) + 1 + C₀ with hr
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : 0 ≤ r := by rw [hr]; nlinarith
  -- Step 1: Kp + X ≤ W^{-Q} (2 + Γ²) N^{1 + C₀}
  have hN1C : 1 ≤ N ^ (1 + C₀) := Real.one_le_rpow hN1 (by linarith)
  have hNN1C : N ≤ N ^ (1 + C₀) := by
    calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ (1 + C₀) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hPMe : Pn * Mi * ex ≤ N ^ C₀ * Γ ^ 2 * W ^ (-Q) := by
    have h1 : Pn * Mi ≤ N ^ C₀ * Γ ^ 2 := mul_le_mul hPn hMi hMi0 (by positivity)
    exact mul_le_mul h1 hex hex0 (by positivity)
  have hX2 : X ≤ W ^ (-Q) * (Γ ^ 2 * N ^ (1 + C₀) + N) := by
    calc X ≤ N * (Pn * Mi * ex + W ^ (-Q)) := hX
      _ ≤ N * (N ^ C₀ * Γ ^ 2 * W ^ (-Q) + W ^ (-Q)) := by gcongr
      _ = W ^ (-Q) * (Γ ^ 2 * (N * N ^ C₀) + N) := by ring
      _ = W ^ (-Q) * (Γ ^ 2 * N ^ (1 + C₀) + N) := by
        rw [Real.rpow_add hN0, Real.rpow_one]
  have hKX : Kp + X ≤ W ^ (-Q) * ((2 + Γ ^ 2) * N ^ (1 + C₀)) := by
    calc Kp + X ≤ W ^ (-Q) + W ^ (-Q) * (Γ ^ 2 * N ^ (1 + C₀) + N) := add_le_add hKp hX2
      _ = W ^ (-Q) * (1 + (Γ ^ 2 * N ^ (1 + C₀) + N)) := by ring
      _ ≤ W ^ (-Q) * ((2 + Γ ^ 2) * N ^ (1 + C₀)) := by
        apply mul_le_mul_of_nonneg_left _ hWQ.le
        nlinarith [sq_nonneg Γ]
  -- Step 2: Λ² ≤ Γ^{2(k-1)} (2+Γ²) N^r W^{-Q}
  have hηpow : ηi ^ (2 * (k - 1)) ≤ (Γ * N) ^ (2 * (k - 1)) := pow_le_pow_left₀ hηi0 hηi _
  have hLpb : Lp ≤ W ^ (-Q) * ((2 + Γ ^ 2) * N ^ (1 + C₀)) := hLp.trans hKX
  have hexp : ((2 * (k - 1) : ℕ) : ℝ) = 2 * ((k : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
  have hNr' : N ^ (2 * (k - 1)) * N ^ (1 + C₀) = N ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0, hexp]
    congr 1; rw [hr]; ring
  have hΛ2 : Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2) * (N ^ r * W ^ (-Q)) := by
    have hηnn : 0 ≤ ηi ^ (2 * (k - 1)) := by positivity
    calc Λ ^ 2 ≤ ηi ^ (2 * (k - 1)) * Lp := hΛ
      _ ≤ (Γ * N) ^ (2 * (k - 1)) * (W ^ (-Q) * ((2 + Γ ^ 2) * N ^ (1 + C₀))) := by
        gcongr
      _ = Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2) * ((N ^ (2 * (k - 1)) * N ^ (1 + C₀)) * W ^ (-Q)) := by
        rw [mul_pow]; ring
      _ = Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2) * (N ^ r * W ^ (-Q)) := by rw [hNr']
  -- Step 3: N^r ≤ W^{A r}, W^{A r} W^{-Q} = W^{-D'}² W⁻¹
  have hNr : N ^ r ≤ W ^ (A * r) := by
    calc N ^ r ≤ (W ^ A) ^ r := Real.rpow_le_rpow hN0.le hNW hr0
      _ = W ^ (A * r) := (Real.rpow_mul hW0.le A r).symm
  have ht0 : 0 < W ^ (-D') := Real.rpow_pos_of_pos hW0 _
  have hWQ' : W ^ (A * r) * W ^ (-Q) = (W ^ (-D')) ^ 2 * W⁻¹ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le,
      ← Real.rpow_neg_one, ← Real.rpow_add hW0]
    congr 1
    rw [hQ]; push_cast; ring
  have hΛ3 : Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2) * ((W ^ (-D')) ^ 2 * W⁻¹) := by
    calc Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2) * (N ^ r * W ^ (-Q)) := hΛ2
      _ ≤ Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2) * (W ^ (A * r) * W ^ (-Q)) := by gcongr
      _ = _ := by rw [hWQ']
  -- Step 4: 2 Λ ≤ W^{-D'}/2
  have hcoef : 4 * (Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2)) * W⁻¹ ≤ 1 / 4 := by
    have h1 : 4 * (Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2)) * W⁻¹ = (16 * Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2)) / (4 * W) := by
      field_simp; ring
    rw [h1, div_le_iff₀ (by positivity)]
    nlinarith
  have h2Λ : 2 * Λ ≤ W ^ (-D') / 2 := by
    have hsq : (2 * Λ) ^ 2 ≤ (W ^ (-D') / 2) ^ 2 := by
      calc (2 * Λ) ^ 2 = 4 * Λ ^ 2 := by ring
        _ ≤ 4 * (Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2) * ((W ^ (-D')) ^ 2 * W⁻¹)) := by gcongr
        _ = (4 * (Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2)) * W⁻¹) * (W ^ (-D')) ^ 2 := by ring
        _ ≤ (1 / 4) * (W ^ (-D')) ^ 2 := by gcongr
        _ = (W ^ (-D') / 2) ^ 2 := by ring
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  -- Step 5: Kc ≤ W^{-D'}/2
  have hKc' : Kc ≤ W ^ (-D') / 2 := by
    have : W ^ (-(D' + 1)) = W ^ (-D') * W⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hW0]; congr 1; ring
    have h3 : W⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW
    calc Kc ≤ W ^ (-(D' + 1)) := hKc
      _ = W ^ (-D') * W⁻¹ := this
      _ ≤ W ^ (-D') * (1 / 2) := by gcongr
      _ = W ^ (-D') / 2 := by ring
  linarith

/-- `exp(-√x) ≤ W^{-Q}` for `x ≥ (W^{τ'/2}/K)²`, eventually in `W` (`log W ≤ W^{τ'/4}/(τ'/4)`). -/
private theorem DecayLoop_exp_small {τ' : ℝ} (hτ' : 0 < τ') {K Q : ℝ} (hK : 0 < K) (hQ : 0 ≤ Q) :
    ∀ᶠ w : ℝ in atTop, ∀ x : ℝ, (w ^ (τ' / 2) / K) ^ 2 ≤ x →
      Real.exp (-Real.sqrt x) ≤ w ^ (-Q) := by
  have hev : ∀ᶠ w : ℝ in atTop, 4 * Q * K / τ' ≤ w ^ (τ' / 4) :=
    (tendsto_rpow_atTop (by linarith : 0 < τ' / 4)).eventually_ge_atTop _
  filter_upwards [hev, eventually_gt_atTop 0] with w hw hw0
  intro x hx
  have hpos : 0 ≤ w ^ (τ' / 2) / K := by positivity
  have hsq : w ^ (τ' / 2) / K ≤ Real.sqrt x := by
    calc w ^ (τ' / 2) / K = Real.sqrt ((w ^ (τ' / 2) / K) ^ 2) := (Real.sqrt_sq hpos).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hlog : Real.log w ≤ w ^ (τ' / 4) / (τ' / 4) :=
    Real.log_le_rpow_div hw0.le (by linarith)
  have hQlog : Q * Real.log w ≤ w ^ (τ' / 2) / K := by
    have h1 : Q * Real.log w ≤ Q * (w ^ (τ' / 4) / (τ' / 4)) := by gcongr
    have h2 : Q * (w ^ (τ' / 4) / (τ' / 4)) = (4 * Q / τ') * w ^ (τ' / 4) := by
      field_simp
    have h3 : w ^ (τ' / 2) = w ^ (τ' / 4) * w ^ (τ' / 4) := by
      rw [← Real.rpow_add hw0]; congr 1; ring
    have hw4 : 0 < w ^ (τ' / 4) := Real.rpow_pos_of_pos hw0 _
    have h4 : (4 * Q / τ') * w ^ (τ' / 4) ≤ w ^ (τ' / 2) / K := by
      rw [h3, le_div_iff₀ hK]
      have : 4 * Q / τ' * K ≤ w ^ (τ' / 4) := by
        have : 4 * Q * K / τ' = 4 * Q / τ' * K := by ring
        linarith
      nlinarith
    linarith
  calc Real.exp (-Real.sqrt x) ≤ Real.exp (-(Q * Real.log w)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = w ^ (-Q) := by
        rw [Real.rpow_def_of_pos hw0]; congr 1; ring

/-! ## 3. The far pair against the decay input and `KcalDecay` -/

/-- `Kpm` is `Kcal` of the `(+,-)` two-loop (`Kn2sol`; `Kcal_two`). -/
private theorem DecayLoop_Kpm_eq {L W : ℕ} [NeZero L] (E u : ℝ) (a b : Z2 L) :
    Kpm L W E u a b = KLoop.Kcal L W E u ⟨[true, false], [a, b]⟩ := by
  rw [KLoop.Kcal_two]
  unfold Kpm
  have : KLoop.mSig E true * KLoop.mSig E false = (Complex.normSq (spectralM E) : ℂ) := by
    simp [KLoop.mSig, Complex.mul_conj]
  rw [this, inv_pow]

/-- The loop of length `2` as a pair of lists. -/
private theorem DecayLoop_loopOf_two {L : ℕ} (s₁ s₂ : Bool) (a b : Z2 L) :
    loopOf (![s₁, s₂] : Fin 2 → Bool) (![a, b] : Fin 2 → Z2 L) = ⟨[s₁, s₂], [a, b]⟩ := by
  simp [loopOf, List.ofFn_succ]

/-- `|a - b|_L ≤ maxDist ![a, b]`. -/
private theorem DecayLoop_zdist2_le_maxDist {L : ℕ} [NeZero L] (a b : Z2 L) :
    zdist2 L (a - b) ≤ KLoop.maxDist L (![a, b] : Fin 2 → Z2 L) := by
  unfold KLoop.maxDist
  exact Finset.le_sup (f := fun p : Fin 2 × Fin 2 => zdist2 L ((![a, b] : Fin 2 → Z2 L) p.1 - (![a, b] : Fin 2 → Z2 L) p.2))
    (Finset.mem_univ ((0 : Fin 2), (1 : Fin 2)))

/-- From `ℓ W^{τ'} ≤ (k-1) δ` and `k - 1 ≤ W^{τ'/2}`: `ℓ W^{τ'/2} ≤ δ` and
`(W^{τ'/2}/k)² ≤ δ/ℓ` (the two thresholds used for `KcalDecay` at length `2` and for the
exponential). -/
private theorem DecayLoop_real_geom {Wr ℓ δ τ' kk : ℝ} (hW : 0 < Wr) (hℓ : 0 < ℓ) (hδ0 : 0 ≤ δ)
    (hk : 2 ≤ kk) (hWk : kk - 1 ≤ Wr ^ (τ' / 2)) (hδ : ℓ * Wr ^ τ' ≤ (kk - 1) * δ) :
    ℓ * Wr ^ (τ' / 2) ≤ δ ∧ (Wr ^ (τ' / 2) / kk) ^ 2 ≤ δ / ℓ := by
  have hs : 0 < Wr ^ (τ' / 2) := Real.rpow_pos_of_pos hW _
  have h1 : Wr ^ τ' = Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by
    rw [← Real.rpow_add hW]; congr 1; ring
  have hk1 : 0 < kk - 1 := by linarith
  constructor
  · have h2 : ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ (kk - 1) * δ := by
      calc ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ ℓ * Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by gcongr
        _ = ℓ * Wr ^ τ' := by rw [h1]; ring
        _ ≤ _ := hδ
    have h3 : ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ δ * (kk - 1) := by linarith
    exact le_of_mul_le_mul_right h3 hk1
  · have hkk : 0 < kk := by linarith
    rw [div_pow, div_le_div_iff₀ (by positivity) hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    have h4 : (τ' / 2) * ((2 : ℕ) : ℝ) = τ' := by push_cast; ring
    rw [h4]
    calc Wr ^ τ' * ℓ = ℓ * Wr ^ τ' := mul_comm _ _
      _ ≤ (kk - 1) * δ := hδ
      _ ≤ kk ^ 2 * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ0
        nlinarith
      _ = δ * kk ^ 2 := mul_comm _ _

/-! ## 4. The probabilistic step, `k ≥ 2` -/

section Main

/-- **`decayLoopAt` for `k ≥ 2`.**  The only random event is that of the decay input at the far pair
`c = c(σ,a)`; on its complement the deterministic chain `DecayLoop_alg` gives
`(|𝓛| + |𝓛-𝒦|)_{u,σ,a} ≤ W^{-D'}`.  Parameters: `τ₁ = 1` for the input, `D = Q` (its `W^{-D}` term),
`KcalDecay` at `(2, τ'/2, Q)` and `(k, τ', D'+1)`. -/
private theorem DecayLoop_main (d : Sizes) {κ c τ C₀ : ℝ} {E u P : ℕ → ℝ}
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hc : 0 < c) (hτ : 0 < τ) (hC₀ : 0 ≤ C₀)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) (hsz : SizeTendsto d) (hbw : Bandwidth d c)
    (hrange : RangeCond d τ u) (hK : KcalDecay κ)
    (hP2 : ∀ᶠ n : ℕ in atTop, P n ≤ ((d.size n : ℕ) : ℝ) ^ C₀)
    (hdec : ∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2)
      (fun n p _ => P n * (scaleM (d.L n) (d.W n) (E n) (u n) ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) / ellT (d.L n) (u n))) +
        (d.W n : ℝ) ^ (-D)))
    {k : ℕ} (hk : 2 ≤ k) {τ' : ℝ} (hτ' : 0 < τ') {D' : ℝ} (hD' : 0 < D') :
    PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p ω =>
        (loopAbs (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2 +
          lkGen (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2) *
        (if ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => (d.W n : ℝ) ^ (-D')) := by
  -- constants
  set Γ : ℝ := 2 / κ with hΓ
  set A : ℝ := 1 / c with hA
  set Q : ℝ := 2 * D' + A * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1 with hQ
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hΓ0 : 0 ≤ Γ := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hQpos : 0 < Q := by
    have : 0 ≤ A * (2 * ((k : ℝ) - 1) + 1 + C₀) := by
      apply mul_nonneg hA0; nlinarith
    linarith
  -- choice of the far pair
  have hpair : ∀ (n : ℕ) (σ : Fin k → Bool) (a : Fin k → Z2 (d.L n)),
      ∃ c : Z2 (d.L n) × Z2 (d.L n),
        ((KLoop.maxDist (d.L n) a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdist2 (d.L n) (c.1 - c.2) : ℝ) ∧
        ∀ (H : Matrix (BlockIndex (d.L n) (d.W n)) (BlockIndex (d.L n) (d.W n)) ℂ) (z : ℂ) (η : ℝ),
          H.IsHermitian → 0 < η → η ≤ |z.im| →
          ‖gloop (d.L n) (d.W n) H z (loopOf σ a)‖ ^ 2 ≤
            η⁻¹ ^ (2 * (k - 1)) * ‖gloop (d.L n) (d.W n) H z ⟨[true, false], [c.1, c.2]⟩‖ :=
    fun n σ a => DecayLoop_pair hk σ a
  choose cp hcp using hpair
  -- the pulled-back source
  have hpb : PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × (Fin k → Bool) × (Fin k → Z2 (d.L n)))
      (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω)
          (cp n p.2.1 p.2.2).1 (cp n p.2.1 p.2.2).2)
      (fun n p _ => P n * (scaleM (d.L n) (d.W n) (E n) (u n) ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((zdist2 (d.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2) : ℝ) /
            ellT (d.L n) (u n))) + (d.W n : ℝ) ^ (-Q)) := by
    intro τ₁ hτ₁ D₁ hD₁
    filter_upwards [hdec Q hQpos τ₁ hτ₁ D₁ hD₁] with n hn p
    exact hn ((), (cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2)
  refine PerTimeCalc.PerTime.perTimeCalc_of_imp hpb ?_
  intro τ₀ hτ₀
  refine ⟨1, one_pos, ?_⟩
  -- eventual facts
  have hsizeN : Tendsto (fun n => d.size n) atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  have hWtend : Tendsto (fun n => (d.W n : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ c) atTop atTop :=
      (tendsto_rpow_atTop hc).comp hsz
    exact tendsto_atTop_mono' _ hbw h1
  have hK2 := hsizeN.eventually (hK hκ c hc 2 (by norm_num) (τ' / 2) Q (by linarith) hQpos)
  have hKk := hsizeN.eventually (hK hκ c hc k (by omega) τ' (D' + 1) hτ' (by linarith))
  have hexp := hWtend.eventually
    (DecayLoop_exp_small (τ' := τ') hτ' (K := (k : ℝ)) (Q := Q) (by linarith) hQpos.le)
  have hW2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (d.W n : ℝ) := hWtend.eventually_ge_atTop 2
  have hWΓ : ∀ᶠ n : ℕ in atTop, 16 * Γ ^ (2 * (k - 1)) * (2 + Γ ^ 2) ≤ (d.W n : ℝ) :=
    hWtend.eventually_ge_atTop _
  have hWk : ∀ᶠ n : ℕ in atTop, (k : ℝ) - 1 ≤ (d.W n : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < τ' / 2)).comp hWtend).eventually_ge_atTop _
  filter_upwards [hK2, hKk, hexp, hW2, hWΓ, hWk, hbw, hrange, hP2] with n hK2n hKkn hexpn hW2n
    hWΓn hWkn hbwn hrn hP2n
  rintro ⟨⟨⟩, σ, a⟩ ω hlt
  by_contra hnot
  dsimp only at hlt hnot
  -- basic facts at the index n
  have hL3 : 3 ≤ d.L n := d.three_le_L n
  have hW1 : 1 ≤ d.W n := d.W_pos n
  have hEn : |E n| < 2 := by linarith [hE n]
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
    have : 0 < d.size n := by
      rw [Sizes.size_eq]; have := d.W_pos n; have := d.three_le_L n; positivity
    exact_mod_cast this
  have hNpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < (d.W n : ℝ) := by linarith
  have hsize : (d.W n) ^ 2 * (d.L n) ^ 2 = d.size n := (Sizes.size_eq d n).symm
  by_cases hfar : ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) a : ℝ)
  swap
  · simp only [hfar, ↓reduceIte, mul_zero] at hlt
    have : 0 < ((d.size n : ℕ) : ℝ) ^ τ₀ * (d.W n : ℝ) ^ (-D') := by positivity
    linarith
  simp only [hfar, ↓reduceIte, mul_one] at hlt
  -- the scales
  obtain ⟨hMlow, hηinv⟩ := scaleM_etaT_of_range (L := d.L n) (W := d.W n) (E := E n) (c := c)
    (τ := τ) (t := u n) (by omega) hW1 hEn hc hτ (hu1 n) hbwn hrn
  have hμpos : 0 < (spectralM (E n)).im := spectralM_im_pos hEn
  have hμ : κ / 2 ≤ (spectralM (E n)).im := by
    rw [spectralM_im]
    have hκ2 : κ ≤ 2 := by have := abs_nonneg (E n); linarith [hE n]
    have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hE n) 2
    have h2 : κ ≤ Real.sqrt (4 - E n ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    linarith
  have hη : 0 < etaT (E n) (u n) := etaT_pos hEn (hu1 n)
  have hηΓ : (etaT (E n) (u n))⁻¹ ≤ Γ * ((d.size n : ℕ) : ℝ) := by
    have hηinv' : (etaT (E n) (u n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (1 - τ) / (spectralM (E n)).im :=
      hηinv
    have h1 : ((d.size n : ℕ) : ℝ) ^ (1 - τ) ≤ ((d.size n : ℕ) : ℝ) := by
      calc _ ≤ ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = _ := Real.rpow_one _
    calc (etaT (E n) (u n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (1 - τ) / (spectralM (E n)).im := hηinv'
      _ ≤ ((d.size n : ℕ) : ℝ) / (spectralM (E n)).im := by gcongr
      _ ≤ ((d.size n : ℕ) : ℝ) / (κ / 2) := by gcongr
      _ = Γ * ((d.size n : ℕ) : ℝ) := by rw [hΓ]; field_simp
  have hMpos : κ / 2 ≤ scaleM (d.L n) (d.W n) (E n) (u n) := by
    have h1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) :=
      Real.one_le_rpow hN1 (le_min (by linarith) hτ.le)
    have hMlow' : (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) ≤
        scaleM (d.L n) (d.W n) (E n) (u n) := hMlow
    calc κ / 2 ≤ (spectralM (E n)).im := hμ
      _ = (spectralM (E n)).im * 1 := (mul_one _).symm
      _ ≤ (spectralM (E n)).im * ((d.size n : ℕ) : ℝ) ^ (min (2 * c) τ) := by gcongr
      _ ≤ _ := hMlow'
  have hMi : (scaleM (d.L n) (d.W n) (E n) (u n) ^ 2)⁻¹ ≤ Γ ^ 2 := by
    have h1 : (κ / 2) ^ 2 ≤ scaleM (d.L n) (d.W n) (E n) (u n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMpos 2
    calc (scaleM (d.L n) (d.W n) (E n) (u n) ^ 2)⁻¹ ≤ ((κ / 2) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) h1
      _ = Γ ^ 2 := by rw [hΓ]; field_simp
  -- the matrix and the far pair
  have hMh : (Sizes.seqHflow d n (u n) ω).IsHermitian := Sizes.seqHflow_isHermitian d n (u n) ω
  have hHh : (blockMat (Sizes.seqHflow d n (u n) ω)).IsHermitian := hMh.submatrix _
  have hzim : etaT (E n) (u n) ≤ |(spectralZ (E n) (u n)).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (by linarith [hu1 n]) hμpos)]
    exact le_of_eq rfl
  obtain ⟨hcmax, hcb⟩ := hcp n σ a
  have hΛ := hcb (blockMat (Sizes.seqHflow d n (u n) ω)) (spectralZ (E n) (u n))
    (etaT (E n) (u n)) hHh hη hzim
  have hℓ1 : 1 ≤ ellT (d.L n) (u n) := one_le_ellT (by omega) (hu0 n) (hu1 n)
  have hℓpos : 0 < ellT (d.L n) (u n) := by linarith
  have hδ : ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤
      ((k : ℝ) - 1) * (zdist2 (d.L n) ((cp n σ a).1 - (cp n σ a).2) : ℝ) := hfar.trans hcmax
  obtain ⟨hfar2, hexarg⟩ := DecayLoop_real_geom hWpos hℓpos (Nat.cast_nonneg _) hk2 hWkn hδ
  -- the bounds on the far pair
  have hKp : ‖Kpm (d.L n) (d.W n) (E n) (u n) (cp n σ a).1 (cp n σ a).2‖ ≤
      (d.W n : ℝ) ^ (-Q) := by
    rw [DecayLoop_Kpm_eq]
    have h := hK2n (d.L n) (d.W n) hL3 hsize hbwn (E n) (hE n) (u n) (hu0 n) (hu1 n)
      ![true, false] ![(cp n σ a).1, (cp n σ a).2]
      (hfar2.trans (by exact_mod_cast DecayLoop_zdist2_le_maxDist (cp n σ a).1 (cp n σ a).2))
    rwa [DecayLoop_loopOf_two] at h
  have hKc := hKkn (d.L n) (d.W n) hL3 hsize hbwn (E n) (hE n) (u n) (hu0 n) (hu1 n) σ a hfar
  have hex := hexpn _ hexarg
  have hLp : ‖gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (u n) ω))
        (spectralZ (E n) (u n)) ⟨[true, false], [(cp n σ a).1, (cp n σ a).2]⟩‖ ≤
      ‖Kpm (d.L n) (d.W n) (E n) (u n) (cp n σ a).1 (cp n σ a).2‖ +
        lkErrMat (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (cp n σ a).1
          (cp n σ a).2 :=
    norm_le_norm_add_norm_sub' _ _
  have hX := not_lt.mp hnot
  rw [Real.rpow_one] at hX
  have hNW : ((d.size n : ℕ) : ℝ) ≤ (d.W n : ℝ) ^ A := by
    calc ((d.size n : ℕ) : ℝ) = (((d.size n : ℕ) : ℝ) ^ c) ^ (1 / c) := by
          rw [← Real.rpow_mul hNpos.le, mul_one_div_cancel hc.ne', Real.rpow_one]
      _ ≤ (d.W n : ℝ) ^ (1 / c) := Real.rpow_le_rpow (by positivity) hbwn (by positivity)
  have key := DecayLoop_alg (W := (d.W n : ℝ)) (N := ((d.size n : ℕ) : ℝ)) (Γ := Γ) (A := A)
    (k := k) (D' := D') (C₀ := C₀) (Q := Q) hk hC₀ hΓ0 hW2n hWΓn hN1 hNW hQ
    (inv_nonneg.mpr hη.le) hηΓ (norm_nonneg _) (norm_nonneg _) hΛ hLp hKp hX hP2n hMi hex
    (inv_nonneg.mpr (sq_nonneg _)) (Real.exp_pos _).le hKc
  have hlk : lkGen (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) σ a ≤
      ‖gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (u n) ω)) (spectralZ (E n) (u n))
        (loopOf σ a)‖ + ‖KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf σ a)‖ := norm_sub_le _ _
  have hlA : loopAbs (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) σ a =
      ‖gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (u n) ω)) (spectralZ (E n) (u n))
        (loopOf σ a)‖ := rfl
  rw [hlA] at hlt
  have hNτ : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ τ₀ := Real.one_le_rpow hN1 hτ₀.le
  have hWD : 0 < (d.W n : ℝ) ^ (-D') := Real.rpow_pos_of_pos hWpos _
  have hle : (d.W n : ℝ) ^ (-D') ≤ ((d.size n : ℕ) : ℝ) ^ τ₀ * (d.W n : ℝ) ^ (-D') :=
    le_mul_of_one_le_left hWD.le hNτ
  linarith

/-- For `k = 1` the far set is empty: `maxDist a = 0`. -/
private theorem DecayLoop_maxDist_one {L : ℕ} [NeZero L] (a : Fin 1 → Z2 L) :
    KLoop.maxDist L a = 0 := by
  unfold KLoop.maxDist
  apply Nat.eq_zero_of_le_zero
  refine Finset.sup_le fun p _ => ?_
  have : p.1 = p.2 := Subsingleton.elim _ _
  simp [this]

end Main

/-! ## 5. The targets -/

section Targets

variable (d : Sizes)

/-- **`lem_decayLoop` (`res_decayLK`) at a single time.**  From the
decay input with polynomial prefactor `P` and `KcalDecay`: for every `k ≥ 1`, `τ', D' > 0`,
`(|𝓛| + |𝓛-𝒦|)_{u,σ,a} 1(ℓ_u W^{τ'} ≤ max|a_i - a_j|) ≺ W^{-D'}`.  The hypotheses
`GbEXPHypV3` and `InitLocal` are not used (see the module docstring). -/
theorem decayLoopAt (κ c τ C₀ : ℝ) (E u P : ℕ → ℝ) : DecayLoopAt d κ c τ C₀ E u P := by
  intro hκ hE hc hτ hC₀ hu0 hu1 hsz hbw hrange hK _hV3 _hP1 hP2 _hloc hdec k hk τ' hτ' D' hD'
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    refine Green.perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_) (fun n _ _ => ?_)
    · have hL : 1 ≤ d.L n := by have := d.three_le_L n; omega
      have hpos : 0 < ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' := by
        have h1 := (ellT_pos_le hL (hu1 n)).1
        have h2 : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
        positivity
      have hmax : (KLoop.maxDist (d.L n) p.2.2 : ℝ) = 0 := by
        rw [DecayLoop_maxDist_one]; simp
      have hnot : ¬ (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) p.2.2 : ℝ)) := by
        rw [hmax]; exact not_le.mpr hpos
      simp only [hnot, ↓reduceIte, mul_zero, le_refl]
    · exact (Real.rpow_pos_of_pos (by exact_mod_cast d.W_pos n) _).le
  · exact DecayLoop_main d hκ hE hc hτ hC₀ hu0 hu1 hsz hbw hrange hK hP2 hdec hk2 hτ' hD'

/-- **The window corollary of `decayLoopAt`**: at every section `u ∈ [s,t]` the
hypotheses of `decayLoopAt` hold with `P = (η_s/η_u)^4 ∈ [1, N^4]` (`C₀ = 4`), from `MainIndHyp`,
`Step2LocalPT`, `Step2DecayPT`; the sections assemble by `perTime_timeIcc_of_forall_seq`. -/
theorem decayLoopWindow (κ c τ : ℝ) (E s t : ℕ → ℝ) : DecayLoopWindow d κ c τ E s t := by
  intro hM hK hV3 hLoc hDec
  obtain ⟨hκ, hE, hc, hτ, hs, hst, ht, hsz, hbw, _, hrange, _, _, _⟩ := hM
  intro k hk τ' hτ' D' hD'
  refine Green.perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size hst
    (V := fun n => (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
    (fun n v q ω => (loopAbs (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2 +
        lkGen (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2) *
      (if ellT (d.L n) v * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) q.2 : ℝ) then 1 else 0))
    (fun n _ _ _ => (d.W n : ℝ) ^ (-D')) ?_
  intro u hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs n).trans (hu n).1
  have hu1 : ∀ n, u n < 1 := fun n => (hu n).2.trans_lt (ht n)
  have hrange_u : RangeCond d τ u := Green.rangeCond_mono d hrange fun n => (hu n).2
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans_lt (ht n)
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hratio : ∀ n, etaT (E n) (s n) / etaT (E n) (u n) = (1 - s n) / (1 - u n) :=
    fun n => etaT_div_etaT (hE2 n) (hs1 n) (hu1 n)
  have hP1 : ∀ n, 1 ≤ (etaT (E n) (s n) / etaT (E n) (u n)) ^ 4 := by
    intro n
    rw [hratio n]
    have h1 : 0 < 1 - u n := by linarith [hu1 n]
    have h2 : 1 ≤ (1 - s n) / (1 - u n) := by
      rw [le_div_iff₀ h1]; linarith [(hu n).1]
    exact one_le_pow₀ h2
  have hP2 : ∀ᶠ n : ℕ in atTop,
      (etaT (E n) (s n) / etaT (E n) (u n)) ^ 4 ≤ ((d.size n : ℕ) : ℝ) ^ (4 : ℝ) := by
    filter_upwards [hrange] with n hn
    have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
      have : 0 < d.size n := by
        rw [Sizes.size_eq]; have := d.W_pos n; have := d.three_le_L n; positivity
      exact_mod_cast this
    have hNpos : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
    have h1 : ((d.size n : ℕ) : ℝ)⁻¹ ≤ 1 - u n := by
      calc ((d.size n : ℕ) : ℝ)⁻¹ = ((d.size n : ℕ) : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
        _ ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ ≤ 1 - t n := hn
        _ ≤ 1 - u n := by linarith [(hu n).2]
    have h2 : 0 < 1 - u n := by linarith [hu1 n]
    have h3 : (1 - s n) / (1 - u n) ≤ ((d.size n : ℕ) : ℝ) := by
      rw [div_le_iff₀ h2]
      have h4 : 1 ≤ ((d.size n : ℕ) : ℝ) * (1 - u n) := by
        have := mul_le_mul_of_nonneg_left h1 hNpos.le
        rwa [mul_inv_cancel₀ hNpos.ne'] at this
      linarith [hs n]
    rw [hratio n, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by
      have : 0 ≤ (1 - s n) := by linarith [hs1 n]
      positivity) h3 4
  have hLoc_u : InitLocal d E u :=
    Green.perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => llErrMat (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n v _ _ => (scaleM (d.L n) (d.W n) (E n) v)⁻¹ ^ ((1 : ℝ) / 2)) hLoc u hu
  have hDec_u : ∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2)
      (fun n p _ => (fun n => (etaT (E n) (s n) / etaT (E n) (u n)) ^ 4) n *
          (scaleM (d.L n) (d.W n) (E n) (u n) ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) / ellT (d.L n) (u n))) +
        (d.W n : ℝ) ^ (-D)) := fun D hD =>
    Green.perSeq_of_perTime_timeIcc (Sizes.seqP d) d.size
      (V := fun n => Z2 (d.L n) × Z2 (d.L n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => lkErrMat (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2)
      (fun n v q _ => (etaT (E n) (s n) / etaT (E n) v) ^ 4 *
          (scaleM (d.L n) (d.W n) (E n) v ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((zdist2 (d.L n) (q.1 - q.2) : ℝ) / ellT (d.L n) v)) +
        (d.W n : ℝ) ^ (-D)) (hDec D hD) u hu
  exact decayLoopAt d κ c τ 4 E u (fun n => (etaT (E n) (s n) / etaT (E n) (u n)) ^ 4)
    hκ hE hc hτ (by norm_num) hu0 hu1 hsz hbw hrange_u hK hV3 hP1 hP2 hLoc_u hDec_u k hk τ' hτ' D' hD'

/-- **The `[0,t]` corollary of `decayLoopAt`**: at every section `0 ≤ u ≤ t`, `MLConcl`
gives `InitLocal` and `InitDecay` (the case `P ≡ 1`, `C₀ = 0`). -/
theorem decayLoopFromML (κ c τ : ℝ) (E t : ℕ → ℝ) : DecayLoopFromML d κ c τ E t := by
  intro hκ hE hc hτ ht0 ht1 hsz hbw hrange hK hV3 hML k hk τ' hτ' D' hD'
  refine Green.perTime_timeIcc_of_forall_seq (Sizes.seqP d) d.size (s := fun _ => 0) (t := t) ht0
    (V := fun n => (Fin k → Bool) × (Fin k → Z2 (d.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
    (fun n v q ω => (loopAbs (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2 +
        lkGen (d.L n) (d.W n) (E n) v (Sizes.seqHflow d n v ω) q.1 q.2) *
      (if ellT (d.L n) v * (d.W n : ℝ) ^ τ' ≤ (KLoop.maxDist (d.L n) q.2 : ℝ) then 1 else 0))
    (fun n _ _ _ => (d.W n : ℝ) ^ (-D')) ?_
  intro u hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hu n).1
  have hu1 : ∀ n, u n < 1 := fun n => (hu n).2.trans_lt (ht1 n)
  have hrange_u : RangeCond d τ u := Green.rangeCond_mono d hrange fun n => (hu n).2
  obtain ⟨⟨_, hinit, hloc⟩, _⟩ := hML u hu0 (fun n => (hu n).2)
  have hdec : ∀ D > (0 : ℝ), PerTimeDomAt (Sizes.seqP d) d.size
      (U := fun n => Unit × Z2 (d.L n) × Z2 (d.L n))
      (fun n p ω => lkErrMat (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2.1 p.2.2)
      (fun n p _ => (fun _ : ℕ => (1 : ℝ)) n * (scaleM (d.L n) (d.W n) (E n) (u n) ^ 2)⁻¹ *
          Real.exp (-Real.sqrt ((zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) / ellT (d.L n) (u n))) +
        (d.W n : ℝ) ^ (-D)) := fun D hD => by
    simpa only [one_mul] using hinit D hD
  exact decayLoopAt d κ c τ 0 E u (fun _ => 1) hκ hE hc hτ le_rfl hu0 hu1 hsz hbw hrange_u hK hV3
    (fun _ => le_rfl) (Filter.Eventually.of_forall fun n => by simp) hloc hdec k hk τ' hτ' D' hD'

end Targets

end RBM.Ind

end
