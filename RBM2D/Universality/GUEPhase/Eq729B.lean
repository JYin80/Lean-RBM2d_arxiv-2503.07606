/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Universality.GUEPhase.Eq729A
import RBM2D.Universality.GUEPhase.OneLoop
import RBM2D.Universality.GUEPhase.KPrim
import RBM2D.Universality.GUEPhase.BootstrapAt
import RBM2D.Evolution.Defs
import RBM2D.Loop.KBound
import RBM2D.Path.ScalesBridge
import RBM2D.Main.ZRescale

/-!
# (7.29) at `t₀` on the GUE-phase grid, second half, and the (7.47) step (`d = 2`)

The crude Grönwall bound, the inputs at the size parameter, the final normalisation, the bad
events, `gueGrid_eq729`, and the (7.47) step: the bound of `OUEq747` from (7.29) and (7.26).  The
first half (the 2-loop algebra, Duhamel in expectation, one grid step of the recursion for `e_k`)
is in `Eq729A.lean`.

## What is proved

* `gueGrid_eq729`: (7.29) at `t₀` on the GUE-phase grid, `σ = (+, σ₂)`: for every `δ > 0`,
  eventually in `n`,
  `‖𝔼 L_{t₀,(+,σ₂),(a,b)} - K̃_{t₀,(+,σ₂),(a,b)}‖ ≤ (d.size n)^δ (N η_{t₀})^{-3}`,
  with `K̃ = kTwoGUE`, from the crude Grönwall with `eq729c`, `eq729_one_step` at `K =
  gueGridK d n0`, the initial term `MLExpConcl d E t₁`, Lemma 5.15 for the
  1-loops (`gueGrid_expect_oneLoop`), `K̃ ≺ Λ^{|I|-1}` from `eq736_detDomAt` and the bad events of
  `GUEPathBounds.lk` (`StochDomAt`).
* `Eq729B_eq747_of_eq729`: (7.29) at `t₀` in the loss form `N^δ (N η_{t₀})^{-3}` at
  `(E', t₁, t₀)`, `E' = lemE z_n`, `t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀`, `z_n = E_n + i η_Q`
  (Lemma 2.8, `z = t₀^{-1/2} z_{t₀}^{(E')}`), together with the law (7.26) at the last grid step
  (`map_gueH_last`, proved here, not an input) and `kTwoGUE_eq_ThetaTilde`, gives the bound of
  `OUEq747` at `(E, t)`: `‖𝔼 tr G E_a G^{(σ)} E_b - profileTilde‖ ≤ W^δ Meta^{-3}`.
* `Eq729B_eq747_of_inputs`: the same from the inputs of `gueGrid_eq729` at `(E', t₁, t₀)`; the
  hypotheses `h730`, `hscale`, `hell`, `Tendsto size`, `|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1` are derived
  from `Admissible 𝔠 d`, `τ_U ≤ ouTauMax 𝔠`, `0 ≤ t_n ≤ ouTStar d τ_U n` (`zztE_quant`).
  `OUEq747 d τ_U` is per sequence `(κ, E, t)`, so this statement is its body.

## Conventions (`d = 2`)

`gueGridK d n0` has base `d.size n + 1`; the initial term is `RBM.Evol.MLExpConcl d E t₁`
(`ML:exp` at `t₁`, scale `scaleM`, `ℓ_{t₁} = L` from `hell`); `KLoop.Kcal`, `KLoop.mSig`;
`K̃₃ ≺ Λ²` from `eq736_detDomAt` on the size scale; the loss in (7.29) is `(d.size n)^δ` (the
conversion to `W^δ` is part of the (7.47) step, `W ≥ N^𝔠`); with `N = (W L)²` the remainder
constant of `eq729c` is `10000 N⁴ (1+N)⁶`.

Helpers are `private` and carry the prefix `Eq729B_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

/-! ### The crude Grönwall bound at a fixed size parameter -/

section PerN

private theorem Eq729B_c_nonneg {N ρ Λ p Δ : ℝ} (hN : 0 ≤ N) (hρ : 0 ≤ ρ) (hΛ : 0 ≤ Λ)
    (hp : 0 ≤ p) (hΔ : 0 ≤ Δ) : 0 ≤ eq729c N ρ Λ p Δ := by
  unfold eq729c
  have : 0 ≤ Δ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ _
  positivity

/-- **The recursion closed by a discrete Grönwall**: at the last grid
step, `‖e_K‖ ≤ exp((t₀ - t₁)·2NρΛ) (e₀ + K c)`, `N = d.size n`. -/
private theorem Eq729B_perN (d : Sizes) {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {n : ℕ}
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hKN : K n ≠ 0)
    {Λ ρ p B0 : ℝ}
    (hΛ : Λ = (((d.size n : ℕ) : ℝ) * etaT (E n) (t0 n))⁻¹) (hΛ1 : Λ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρΛ : ρ * Λ ≤ 1) (hp0 : 0 ≤ p)
    (hMΔ : ((d.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1)
    (hK2b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ)
    (hK3b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w,
      ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2)
    (hKd : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
        (primRhsGUE (d.L n) (d.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩)
        (Set.Icc (t1 n) (t0 n)) s)
    (hX : ∀ k < K n, ∀ a,
      ‖(∫ ω, eq729F d t1 t0 K E n k ω ⟨[true], [a]⟩ ∂(Pgue d)) - spectralM (E n)‖ ≤ ρ * Λ ^ 2)
    {B : Set (PathΩ d)} (hB : Pgue d B ≤ ENNReal.ofReal p)
    (hg1 : ∀ ω ∉ B, ∀ k < K n, ∀ σ a,
      ‖eq729F d t1 t0 K E n k ω ⟨[σ], [a]⟩ - KLoop.mSig (E n) σ‖ ≤ ρ * Λ)
    (hg2 : ∀ ω ∉ B, ∀ k < K n, ∀ s1 s2 x y, ‖eq729F d t1 t0 K E n k ω ⟨[s1, s2], [x, y]⟩
      - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2)
    (hg3 : ∀ ω ∉ B, ∀ k < K n, ∀ s1 s2 s3 x y w,
      ‖eq729F d t1 t0 K E n k ω ⟨[s1, s2, s3], [x, y, w]⟩
        - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 3)
    (hinit : ∀ s1 s2 x y, ‖eq729e d t1 t0 K E Kt n 0 ⟨[s1, s2], [x, y]⟩‖ ≤ B0)
    (s1 s2 : Bool) (a1 a2 : Z2 (d.L n)) :
    ‖eq729e d t1 t0 K E Kt n (K n) ⟨[s1, s2], [a1, a2]⟩‖ ≤
      Real.exp ((t0 n - t1 n) * (2 * ((d.size n : ℕ) : ℝ) * (ρ * Λ))) *
        (B0 + (K n : ℝ) * eq729c ((d.size n : ℕ) : ℝ) ρ Λ p (gridStep t1 t0 K n)) := by
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hN
  set Δ : ℝ := gridStep t1 t0 K n with hΔ
  set r : ℝ := 2 * N * (ρ * Λ) with hr
  set c : ℝ := eq729c N ρ Λ p Δ with hc
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hΔ0 : 0 ≤ Δ := eq729_step_nonneg ht10
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]; exact inv_nonneg.2 (mul_nonneg hN0 (eq729_eta_pos hE ht0).le)
  have hr0 : 0 ≤ r := by positivity
  have hc0 : 0 ≤ c := Eq729B_c_nonneg hN0 hρ0 hΛ0 hp0 hΔ0
  have hB00 : 0 ≤ B0 := (norm_nonneg _).trans (hinit true true 0 0)
  have hq1 : 1 ≤ 1 + Δ * r := by nlinarith
  have claim : ∀ k, k ≤ K n → ∀ s1 s2 x y,
      ‖eq729e d t1 t0 K E Kt n k ⟨[s1, s2], [x, y]⟩‖ ≤ (1 + Δ * r) ^ k * (B0 + k * c) := by
    intro k
    induction k with
    | zero =>
      intro _ s1 s2 x y
      simpa using hinit s1 s2 x y
    | succ k ih =>
      intro hk s1 s2 x y
      have hk' : k < K n := hk
      have hstep := eq729_one_step d K Kt hE ht1 ht10 ht0 hΛ hΛ1 hρ0 hρΛ hp0 hMΔ hK2b hK3b hKd
        hk' (hX k hk') hB (fun ω hω => hg1 ω hω k hk') (fun ω hω => hg2 ω hω k hk')
        (fun ω hω => hg3 ω hω k hk') (ih hk'.le) s1 s2 x y
      refine hstep.trans ?_
      have hpow : 1 ≤ (1 + Δ * r) ^ (k + 1) := one_le_pow₀ hq1
      have hA : 0 ≤ B0 + k * c := by positivity
      rw [Nat.cast_succ]
      calc (1 + Δ * r) * ((1 + Δ * r) ^ k * (B0 + k * c)) + c
          = (1 + Δ * r) ^ (k + 1) * (B0 + k * c) + c := by ring
        _ ≤ (1 + Δ * r) ^ (k + 1) * (B0 + k * c) + (1 + Δ * r) ^ (k + 1) * c := by
            gcongr; exact le_mul_of_one_le_left hc0 hpow
        _ = (1 + Δ * r) ^ (k + 1) * (B0 + (k + 1) * c) := by ring
  refine (claim (K n) le_rfl s1 s2 a1 a2).trans ?_
  have hexp : (1 + Δ * r) ^ (K n) ≤ Real.exp ((t0 n - t1 n) * r) := by
    have h1 : 1 + Δ * r ≤ Real.exp (Δ * r) := by linarith [Real.add_one_le_exp (Δ * r)]
    calc (1 + Δ * r) ^ (K n) ≤ Real.exp (Δ * r) ^ (K n) := pow_le_pow_left₀ (by linarith) h1 _
      _ = Real.exp ((K n : ℝ) * (Δ * r)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp ((t0 n - t1 n) * r) := by rw [← mul_assoc, hΔ, eq729_KΔ hKN]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

end PerN

/-! ### Inputs at the size parameter `n`: `K̃` on 1-, 2-, 3-loops and the initial term -/

section Inputs

variable (d : Sizes)

/-- `K̃` on 1-loops is the constant `m(σ)`: `primRhsGUE` of a 1-loop vanishes. -/
private theorem Eq729B_Kt_one {E t1 t0 : ℕ → ℝ} (n0 : ℕ) (hn0 : 3 ≤ n0) (n : ℕ)
    (ht10 : t1 n ≤ t0 n)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t) :
    ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ σ a, Kt n s ⟨[σ], [a]⟩ = KLoop.mSig (E n) σ := by
  intro s hs σ a
  have h := (convex_Icc (t1 n) (t0 n)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => Kt n s ⟨[σ], [a]⟩)
    (f' := fun s => primRhsGUE (d.L n) (d.W n) (Kt n s) ⟨[σ], [a]⟩) (C := 0)
    (fun r hr => hK n r hr _ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega))
    (fun r _ => by rw [eq729_primRhs_one, norm_zero]) ⟨le_rfl, ht10⟩ hs
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  rw [h, hKinit]
  simp [KLoop.Kcal, KLoop.Kgen, LoopIdx.length]

private theorem Eq729B_size_pos (n : ℕ) : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by
  have h1 : 0 < d.size n := by
    unfold Sizes.size
    have hW := d.W_pos n
    have hL := d.three_le_L n
    positivity
  exact_mod_cast h1

private theorem Eq729B_nine_le_size (n : ℕ) : 9 ≤ d.size n := by
  unfold Sizes.size
  have hW := d.W_pos n
  have hL := d.three_le_L n
  have h3 : 3 ≤ d.W n * d.L n := by nlinarith
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ (d.W n * d.L n) ^ 2 := Nat.pow_le_pow_left h3 2

private theorem Eq729B_gueScale_pos {E : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2) {t : ℝ} (ht : t < 1) :
    0 < gueScale d E n t := by
  unfold gueScale
  exact mul_pos (Eq729B_size_pos d n) (eq729_eta_pos hE ht)

private theorem Eq729B_gueScale_anti {E : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2) {u t : ℝ}
    (hut : u ≤ t) : gueScale d E n t ≤ gueScale d E n u := by
  unfold gueScale
  exact mul_le_mul_of_nonneg_left (eq729_eta_le hE hut) (Nat.cast_nonneg _)

private theorem Eq729B_inv_scale_le {E : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2) {u t : ℝ}
    (hut : u ≤ t) (ht : t < 1) : (gueScale d E n u)⁻¹ ≤ (gueScale d E n t)⁻¹ :=
  inv_anti₀ (Eq729B_gueScale_pos d hE ht) (Eq729B_gueScale_anti d hE hut)

private theorem Eq729B_ofFn_getD {α : Type*} (l : List α) (dflt : α) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i dflt) = l := by
  subst h
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  simp

/-- A well-formed loop is `KLoop.loopOf` of its own signs and labels. -/
private theorem Eq729B_loopOf_eq {L : ℕ} [NeZero L] (J : LoopIdx (Z2 L)) (hJ : J.WF) :
    KLoop.loopOf L (fun i : Fin J.length => J.σ.getD i false)
      (fun i : Fin J.length => J.a.getD i 0) = J := by
  obtain ⟨σ', a'⟩ := J
  simp only [LoopIdx.WF] at hJ
  simp only [KLoop.loopOf, LoopIdx.length]
  rw [Eq729B_ofFn_getD σ' false a'.length hJ, Eq729B_ofFn_getD a' 0 a'.length rfl]

/-- The initial data of `K̃` at `t₁`: `‖Kcal_{t₁, I}‖ ≤ N^{τ'} (N η_{t₁})^{-|I|+1}` for loops of
length in `[2, m]`, from `Kbound_prec_uncond` at the parameter point `(d.L n, d.W n, E n, t1 n)` of
`KLoop.Par κ (d.size n)` and `ℓ_{t₁} = L` (`hell`).  Copy of the private `Proc_initial`
(`Proc.lean`) with the length range `[2, m]`. -/
private theorem Eq729B_initial {κ : ℝ} (hκ : 0 < κ) (m : ℕ) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto d.size atTop atTop)
    (hell : ∀ᶠ n : ℕ in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ n : ℕ in atTop, ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 2 ≤ I.length → I.length ≤ m →
      ‖Kt n (t1 n) I‖ ≤ ((d.size n : ℕ) : ℝ) ^ τ' * (gueScale d E n (t1 n))⁻¹ ^ (I.length - 1) := by
  have hall : ∀ᶠ N : ℕ in atTop, ∀ ℓ ∈ Finset.Icc 2 m,
      ∀ x : (p : KLoop.Par κ N) × (Fin ℓ → Bool) × (Fin ℓ → Z2 p.L),
        ‖KLoop.Kcal x.1.L x.1.W x.1.E x.1.t (KLoop.loopOf x.1.L x.2.1 x.2.2)‖ ≤
          (N : ℝ) ^ τ' * (KLoop.Mt x.1.L x.1.W x.1.E x.1.t)⁻¹ ^ (ℓ - 1) :=
    (Filter.eventually_all_finset _).2 fun ℓ hℓ =>
      KLoop.Kbound_prec_uncond ℓ (by have := (Finset.mem_Icc.1 hℓ).1; omega) κ hκ τ' hτ'
  filter_upwards [hsz.eventually hall, hell] with n hn hellN I hWF h2 h2n
  have ht1lt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hIlen : I.length ∈ Finset.Icc 2 m := Finset.mem_Icc.2 ⟨h2, h2n⟩
  let par : KLoop.Par κ (d.size n) :=
    { L := d.L n, W := d.W n, hL := d.three_le_L n, hW := d.W_pos n,
      hN := (Sizes.size_eq d n).symm, E := E n, hE := hE n, t := t1 n,
      ht0 := ht1 n, ht1 := ht1lt }
  have hx := hn I.length hIlen
    ⟨par, fun i : Fin I.length => I.σ.getD i false, fun i : Fin I.length => I.a.getD i 0⟩
  have hx' : ‖KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n)
        (KLoop.loopOf (d.L n) (fun i : Fin I.length => I.σ.getD i false)
          (fun i : Fin I.length => I.a.getD i 0))‖ ≤
      ((d.size n : ℕ) : ℝ) ^ τ' * (KLoop.Mt (d.L n) (d.W n) (E n) (t1 n))⁻¹ ^ (I.length - 1) := hx
  rw [Eq729B_loopOf_eq I hWF] at hx'
  have hMt : KLoop.Mt (d.L n) (d.W n) (E n) (t1 n) = gueScale d E n (t1 n) := by
    rw [kloop_Mt_eq ht1lt.le]
    unfold scaleM gueScale
    rw [ellT_eq_L ht1lt hellN, Sizes.size_eq]
    push_cast
    ring
  rw [hKinit n I, ← hMt]
  exact hx'

/-- **(7.36)** for lengths `2, 3` on the size scale: `K̃ ≺ (N η_s)^{-|I|+1}` uniformly on
`[t₁, t₀]`. -/
private theorem Eq729B_K_bounds {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    {E t1 t0 : ℕ → ℝ} (hsize : Tendsto (fun n => d.size n) atTop atTop)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hell : ∀ᶠ n : ℕ in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF →
      2 ≤ I.length → I.length ≤ 3 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t) :
    ∀ τ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1 n) (t0 n),
      (∀ s1 s2 x y, ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤
        ((d.size n : ℕ) : ℝ) ^ τ * (gueScale d E n s)⁻¹) ∧
      (∀ s1 s2 s3 x y w, ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖
        ≤ ((d.size n : ℕ) : ℝ) ^ τ * (gueScale d E n s)⁻¹ ^ 2) := by
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hlam : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), 0 < gueScale d E n t := fun n t ht =>
    Eq729B_gueScale_pos d (hE2 n) (lt_of_le_of_lt ht.2 (ht0 n))
  have hanti : ∀ n, ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ t ∈ Set.Icc (t1 n) (t0 n), u ≤ t →
      gueScale d E n t ≤ gueScale d E n u := fun n u _ t _ hut =>
    Eq729B_gueScale_anti d (hE2 n) hut
  have hlamc : ∀ n, ContinuousOn (gueScale d E n) (Set.Icc (t1 n) (t0 n)) := by
    intro n
    have heq : gueScale d E n = fun t => ((d.size n : ℕ) : ℝ) * ((1 - t) * (spectralM (E n)).im) :=
      rfl
    rw [heq]
    exact (by fun_prop : Continuous fun t : ℝ =>
      ((d.size n : ℕ) : ℝ) * ((1 - t) * (spectralM (E n)).im)).continuousOn
  have h730' : ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n),
      (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) * (t - t1 n) ≤
        ((d.size n : ℕ) : ℝ) ^ (-τU) * gueScale d E n t := by
    filter_upwards [h730] with n hn t ht
    have hN0 : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : t - t1 n ≤ t0 n - t1 n := by linarith [ht.2]
    have h2' : etaT (E n) (t0 n) ≤ etaT (E n) t := eq729_eta_le (hE2 n) ht.2
    have hNpow : (0 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) := Real.rpow_nonneg hN0 _
    have h3 : t - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) t :=
      le_trans h1 (le_trans hn (mul_le_mul_of_nonneg_left h2' hNpow))
    have e : (((d.W n * d.L n) ^ 2 : ℕ) : ℝ) = ((d.size n : ℕ) : ℝ) := rfl
    rw [e]
    unfold gueScale
    calc ((d.size n : ℕ) : ℝ) * (t - t1 n)
        ≤ ((d.size n : ℕ) : ℝ) * (((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) t) :=
          mul_le_mul_of_nonneg_left h3 hN0
      _ = ((d.size n : ℕ) : ℝ) ^ (-τU) * (((d.size n : ℕ) : ℝ) * etaT (E n) t) := by ring
  have h732 : UnifDetDomAt d.size (fun n (I : LoopSet (d.L n) 3) => ‖Kt n (t1 n) I.1‖)
      (fun n I => (gueScale d E n (t1 n))⁻¹ ^ (I.1.length - 1)) := by
    intro τ hτ
    filter_upwards [Eq729B_initial d hκ 3 hE ht1 ht10 ht0 hsize hell Kt hKinit hτ] with n hn
    rintro ⟨I, hWF, h2, h3⟩
    exact hn I hWF h2 h3
  have key := eq736_detDomAt d.size hsize d.L d.W Kt 3 t1 t0 ht10 (gueScale d E) hlam hanti hlamc hK
    hτU h730' h732
  intro τ hτ
  filter_upwards [key τ hτ] with n hN s hs
  refine ⟨fun s1 s2 x y => ?_, fun s1 s2 s3 x y w => ?_⟩
  · have := hN (⟨s, hs⟩, ⟨⟨[s1, s2], [x, y]⟩, rfl, by simp [LoopIdx.length],
      by simp [LoopIdx.length]⟩)
    simpa [LoopIdx.length] using this
  · have := hN (⟨s, hs⟩, ⟨⟨[s1, s2, s3], [x, y, w]⟩, rfl, by simp [LoopIdx.length],
      by simp [LoopIdx.length]⟩)
    simpa [LoopIdx.length] using this

/-- **The only transfer between carriers**: the one-time law at step `0` (`map_gueH_zero`). -/
private theorem Eq729B_transfer (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (ht1 : 0 ≤ t1 n) (z : ℂ)
    (I : LoopIdx (Z2 (d.L n))) :
    ∫ ω, gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n 0 ω)) z I ∂(Pgue d)
      = ∫ ω, gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (t1 n) ω)) z I
          ∂(Sizes.seqP d) := by
  have hc : Measurable fun M : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ =>
      gloop (d.L n) (d.W n) (blockMat M) z I := GoodEvent_measurable_gloop (d.L n) (d.W n) z I
  have hHf : Measurable (Sizes.seqHflow d n (t1 n)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      Sizes.measurable_seqHflow_entry d n (t1 n) i j
  calc ∫ ω, gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n 0 ω)) z I ∂(Pgue d)
      = ∫ M, gloop (d.L n) (d.W n) (blockMat M) z I ∂((Pgue d).map (gueH d t1 t0 K n 0)) :=
        (integral_map (gueH_measurable d t1 t0 K n 0).aemeasurable
          hc.aestronglyMeasurable).symm
    _ = ∫ M, gloop (d.L n) (d.W n) (blockMat M) z I
          ∂((Sizes.seqP d).map (Sizes.seqHflow d n (t1 n))) := by
        rw [map_gueH_zero d t1 t0 K n ht1]
    _ = ∫ ω, gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (t1 n) ω)) z I
          ∂(Sizes.seqP d) :=
        integral_map hHf.aemeasurable hc.aestronglyMeasurable

end Inputs

/-! ### The final normalisation -/

section Arith

/-- `exp 2 < 7.4`. -/
private theorem Eq729B_exp_two_lt : Real.exp 2 < 7.4 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

/-- **The final normalisation**: `exp(E₀·2NρΛ)(ρΛ³ + K c) ≤ 56 ρ Λ³`, `K = (N+1)^{2A}`, `A ≥ 80`,
`p = 3/N¹²`, `N ≥ 9`. -/
private theorem Eq729B_arith {N : ℕ} (hN : 9 ≤ N) {ρ Λ E0 Δ Kr : ℝ} (A : ℕ) (hA : 80 ≤ A)
    (hKr : Kr = ((N : ℝ) + 1) ^ (2 * A)) (hρ : 1 ≤ ρ)
    (hΛ0 : 0 < Λ) (hΛN : 1 ≤ (N : ℝ) * Λ) (hE01 : E0 ≤ 1) (hKΔ : Kr * Δ = E0)
    (hΔ0 : 0 ≤ Δ) (hθ : E0 * (N : ℝ) * Λ * ρ ≤ 1) :
    Real.exp (E0 * (2 * (N : ℝ) * (ρ * Λ))) *
        (ρ * Λ ^ 3 + Kr * eq729c (N : ℝ) ρ Λ (3 / (N : ℝ) ^ 12) Δ) ≤ 56 * ρ * Λ ^ 3 := by
  set x : ℝ := (N : ℝ) with hx
  have hx9 : 9 ≤ x := by rw [hx]; exact_mod_cast hN
  have hx4 : 4 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x + 1 := by linarith
  have hKr0 : 0 < Kr := by rw [hKr]; positivity
  have hρ0 : 0 ≤ ρ := by linarith
  have hΛ3 : 1 / x ^ 3 ≤ Λ ^ 3 := by
    have h1 : 1 / x ≤ Λ := by rw [div_le_iff₀ hx0]; linarith
    calc 1 / x ^ 3 = (1 / x) ^ 3 := by rw [_root_.one_div_pow]
      _ ≤ Λ ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  -- the exponential factor
  have hexp : Real.exp (E0 * (2 * x * (ρ * Λ))) ≤ 7.4 := by
    have : E0 * (2 * x * (ρ * Λ)) ≤ 2 := by
      have e : E0 * (2 * x * (ρ * Λ)) = 2 * (E0 * x * Λ * ρ) := by ring
      rw [e]; linarith
    exact ((Real.exp_le_exp.2 this).trans Eq729B_exp_two_lt.le)
  -- the pieces of `K c`
  have hsqrt : Δ ^ ((3 : ℝ) / 2) = Δ * Real.sqrt Δ := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hΔ0 (by norm_num), Real.rpow_one]
  have hΔK : Δ ≤ 1 / Kr := by
    rw [le_div_iff₀ hKr0]; linarith [mul_comm Kr Δ]
  have hsqrtΔ : Real.sqrt Δ ≤ 1 / (x + 1) ^ A := by
    have h1 : Real.sqrt (1 / Kr) = 1 / (x + 1) ^ A := by
      rw [hKr, pow_mul', one_div, Real.sqrt_inv, Real.sqrt_sq (by positivity), one_div]
    rw [← h1]; exact Real.sqrt_le_sqrt hΔK
  have hpow80 : (x + 1) ^ 80 ≤ (x + 1) ^ A := pow_le_pow_right₀ hx1 hA
  -- piece Q2 + Q3 (main)
  have hXeq : eq729c x ρ Λ (3 / x ^ 12) Δ
      = Δ * (5 * x * ρ ^ 2 * Λ ^ 4 + 36 * x ^ 5 / x ^ 12)
        + 10000 * x ^ 4 * (1 + x) ^ 6 * Δ ^ ((3 : ℝ) / 2) + 3 * x ^ 2 * Δ ^ 2 := by
    unfold eq729c; ring
  have hmain : E0 * (5 * x * ρ ^ 2 * Λ ^ 4) ≤ 5 * ρ * Λ ^ 3 := by
    have h : E0 * (5 * x * ρ ^ 2 * Λ ^ 4) = 5 * ρ * Λ ^ 3 * (E0 * x * Λ * ρ) := by ring
    rw [h]
    have : 0 ≤ 5 * ρ * Λ ^ 3 := by positivity
    exact mul_le_of_le_one_right this hθ
  have hbad : E0 * (36 * x ^ 5 / x ^ 12) ≤ 1 / (3 * x ^ 3) := by
    have h1 : E0 * (36 * x ^ 5 / x ^ 12) ≤ 36 * x ^ 5 / x ^ 12 := by
      have : 0 ≤ 36 * x ^ 5 / x ^ 12 := by positivity
      calc E0 * (36 * x ^ 5 / x ^ 12) ≤ 1 * (36 * x ^ 5 / x ^ 12) :=
            mul_le_mul_of_nonneg_right hE01 this
        _ = 36 * x ^ 5 / x ^ 12 := one_mul _
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hx4' : (256 : ℝ) ≤ x ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hx4 4
      norm_num at this; linarith
    have h8 : 0 < x ^ 8 := by positivity
    calc 36 * x ^ 5 * (3 * x ^ 3) = 108 * x ^ 8 := by ring
      _ ≤ 256 * x ^ 8 := by linarith
      _ ≤ x ^ 4 * x ^ 8 := mul_le_mul_of_nonneg_right hx4' h8.le
      _ = 1 * x ^ 12 := by ring
  -- piece Q4, Taylor
  have htaylor : Kr * (10000 * x ^ 4 * (1 + x) ^ 6 * Δ ^ ((3 : ℝ) / 2))
      ≤ 1 / (3 * x ^ 3) := by
    rw [hsqrt]
    have hsΔ0 : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
    have e : Kr * (10000 * x ^ 4 * (1 + x) ^ 6 * (Δ * Real.sqrt Δ))
        = 10000 * x ^ 4 * (1 + x) ^ 6 * (Kr * Δ) * Real.sqrt Δ := by ring
    rw [e, hKΔ]
    have h1 : 10000 * x ^ 4 * (1 + x) ^ 6 * E0 * Real.sqrt Δ
        ≤ 10000 * x ^ 4 * (1 + x) ^ 6 * 1 * (1 / (x + 1) ^ A) := by
      gcongr
    refine h1.trans ?_
    rw [mul_one, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    -- `3 · 10⁴ x⁷ (1+x)⁶ ≤ (x+1)^A`
    have hx7 : x ^ 7 ≤ (x + 1) ^ 7 := pow_le_pow_left₀ hx0.le (by linarith) 7
    have h5 : (30000 : ℝ) ≤ (x + 1) ^ 7 := by
      calc (30000 : ℝ) ≤ 10 ^ 7 := by norm_num
        _ ≤ (x + 1) ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
    have hA' : 10000 * x ^ 4 * (1 + x) ^ 6 * (3 * x ^ 3) = 30000 * x ^ 7 * (x + 1) ^ 6 := by ring
    rw [hA']
    calc 30000 * x ^ 7 * (x + 1) ^ 6 ≤ (x + 1) ^ 7 * (x + 1) ^ 7 * (x + 1) ^ 6 := by gcongr
      _ = (x + 1) ^ 20 := by rw [← pow_add, ← pow_add]
      _ ≤ (x + 1) ^ A := pow_le_pow_right₀ hx1 (by omega)
      _ = 1 * (x + 1) ^ A := (one_mul _).symm
  -- piece Q4, primitive side
  have hkdisc : Kr * (3 * x ^ 2 * Δ ^ 2) ≤ 1 / (3 * x ^ 3) := by
    have e : Kr * (3 * x ^ 2 * Δ ^ 2) = 3 * x ^ 2 * (Kr * Δ) * Δ := by ring
    rw [e, hKΔ]
    have h1 : 3 * x ^ 2 * E0 * Δ ≤ 3 * x ^ 2 * 1 * (1 / Kr) := by gcongr
    refine h1.trans ?_
    rw [mul_one, mul_one_div, div_le_div_iff₀ hKr0 (by positivity), hKr]
    have hx5 : x ^ 5 ≤ (x + 1) ^ 5 := pow_le_pow_left₀ hx0.le (by linarith) 5
    have h9 : (9 : ℝ) ≤ (x + 1) ^ 2 := by
      calc (9 : ℝ) ≤ 10 ^ 2 := by norm_num
        _ ≤ (x + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have h160 : (x + 1) ^ 7 ≤ (x + 1) ^ (2 * A) := pow_le_pow_right₀ hx1 (by omega)
    calc 3 * x ^ 2 * (3 * x ^ 3) = 9 * x ^ 5 := by ring
      _ ≤ (x + 1) ^ 2 * (x + 1) ^ 5 := by gcongr
      _ = (x + 1) ^ 7 := by rw [← pow_add]
      _ ≤ (x + 1) ^ (2 * A) := h160
      _ = 1 * (x + 1) ^ (2 * A) := (one_mul _).symm
  -- assembly
  have hKc : Kr * eq729c x ρ Λ (3 / x ^ 12) Δ ≤ 5 * ρ * Λ ^ 3 + Λ ^ 3 := by
    rw [hXeq]
    have e : Kr * (Δ * (5 * x * ρ ^ 2 * Λ ^ 4 + 36 * x ^ 5 / x ^ 12)
        + 10000 * x ^ 4 * (1 + x) ^ 6 * Δ ^ ((3 : ℝ) / 2) + 3 * x ^ 2 * Δ ^ 2)
        = (Kr * Δ) * (5 * x * ρ ^ 2 * Λ ^ 4) + (Kr * Δ) * (36 * x ^ 5 / x ^ 12)
          + Kr * (10000 * x ^ 4 * (1 + x) ^ 6 * Δ ^ ((3 : ℝ) / 2))
          + Kr * (3 * x ^ 2 * Δ ^ 2) := by ring
    rw [e, hKΔ]
    have hsum : 1 / (3 * x ^ 3) + 1 / (3 * x ^ 3) + 1 / (3 * x ^ 3) = 1 / x ^ 3 := by
      field_simp; ring
    linarith
  have hin : 0 ≤ ρ * Λ ^ 3 + Kr * eq729c x ρ Λ (3 / x ^ 12) Δ := by
    have := Eq729B_c_nonneg hx0.le hρ0 hΛ0.le (by positivity : (0 : ℝ) ≤ 3 / x ^ 12) hΔ0
    positivity
  have hρΛ3 : Λ ^ 3 ≤ ρ * Λ ^ 3 := le_mul_of_one_le_left (by positivity) hρ
  calc Real.exp (E0 * (2 * x * (ρ * Λ))) * (ρ * Λ ^ 3 + Kr * eq729c x ρ Λ (3 / x ^ 12) Δ)
      ≤ 7.4 * (ρ * Λ ^ 3 + Kr * eq729c x ρ Λ (3 / x ^ 12) Δ) :=
        mul_le_mul_of_nonneg_right hexp hin
    _ ≤ 7.4 * (7 * (ρ * Λ ^ 3)) := by gcongr; linarith
    _ = 51.8 * (ρ * Λ ^ 3) := by ring
    _ ≤ 56 * (ρ * Λ ^ 3) := by
        have : 0 ≤ ρ * Λ ^ 3 := by positivity
        linarith
    _ = 56 * ρ * Λ ^ 3 := by ring

end Arith

/-! ### The bad events of `GUEPathBounds.lk` -/

section Bad

variable (d : Sizes)

/-- The failure event of `hP.lk m` at level `τ`, size index `n`. -/
private def Eq729B_Bad (E t1 t0 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ) (n0 m : ℕ)
    (τ : ℝ) (n : ℕ) : Set (PathΩ d) :=
  {ω | ∃ p : Fin (gueGridK d n0 n + 1) × (Fin m → Bool) × (Fin m → Z2 (d.L n)),
    ((d.size n : ℕ) : ℝ) ^ τ *
        (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n p.1))⁻¹ ^ m <
      ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n p.1 ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n p.1)) (loopOf p.2.1 p.2.2) -
        Kt n (gridTime t1 t0 (gueGridK d n0) n p.1) (loopOf p.2.1 p.2.2)‖}

private theorem Eq729B_not_bad {E t1 t0 : ℕ → ℝ} {Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ}
    {n0 m n : ℕ} {τ : ℝ} {ω : PathΩ d} (hω : ω ∉ Eq729B_Bad d E t1 t0 Kt n0 m τ n) {k : ℕ}
    (hk : k ≤ gueGridK d n0 n) (σ : Fin m → Bool) (a : Fin m → Z2 (d.L n)) :
    ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n k ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k)) (loopOf σ a) -
        Kt n (gridTime t1 t0 (gueGridK d n0) n k) (loopOf σ a)‖
      ≤ ((d.size n : ℕ) : ℝ) ^ τ *
        (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ m := by
  by_contra h
  exact hω ⟨(⟨k, Nat.lt_succ_of_le hk⟩, σ, a), lt_of_not_ge h⟩

end Bad

/-! ### The statement `gueGrid_eq729` -/

/-- **(7.29) at `t₀` on the GUE-phase grid** ([YY_25] §7.2, cited by the paper in the resolvent
estimates after `417`), `σ = (+, σ₂)`, on the size scale `N = d.size n = (W L)²`, with
`GUEPathBounds`, `gueGridK` and the initial term `MLExpConcl d E t1` (`ML:exp` at `t₁`). -/
theorem gueGrid_eq729 (d : Sizes) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 3 ≤ n0)
    {E t1 t0 : ℕ → ℝ} (hsize : Tendsto (fun n => d.size n) atTop atTop)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale d E n (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E n) (t1 n) I)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hK2 : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Z2 (d.L n)),
      Kt n t ⟨[σ₁, σ₂], [a, b]⟩ =
        kTwoGUE (d.L n) (d.W n) (KLoop.mSig (E n)) (t1 n) t σ₁ σ₂ a b)
    (hB : RBM.Evol.MLExpConcl d E t1) (hP : GUEPathBounds d E t1 t0 (gueGridK d n0) n0 Kt) :
    ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (σ₂ : Bool) (a b : Z2 (d.L n)),
      ‖(∫ ω, gloop (d.L n) (d.W n)
            (blockMat (gueH d t1 t0 (gueGridK d n0) n (gueGridK d n0 n) ω))
            (spectralZ (E n) (t0 n)) ⟨[true, σ₂], [a, b]⟩ ∂(Pgue d)) -
        kTwoGUE (d.L n) (d.W n) (KLoop.mSig (E n)) (t1 n) (t0 n) true σ₂ a b‖ ≤
      ((d.size n : ℕ) : ℝ) ^ δ * (gueScale d E n (t0 n))⁻¹ ^ 3 := by
  intro δ hδ
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  set τ : ℝ := min (δ / 4) τU with hτdef
  have hτ : 0 < τ := lt_min (by positivity) hτU
  have hττU : τ ≤ τU := min_le_right _ _
  have hτδ : τ ≤ δ / 4 := min_le_left _ _
  have hKne := gueGridK_ne_zero d n0
  have hKone : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ σ a, Kt n s ⟨[σ], [a]⟩ = KLoop.mSig (E n) σ :=
    fun n => Eq729B_Kt_one d n0 hn0 n (ht10 n) Kt hKinit hK
  have hKmem : ∀ n k, k ≤ gueGridK d n0 n →
      gridTime t1 t0 (gueGridK d n0) n k ∈ Set.Icc (t1 n) (t0 n) := fun n k hk =>
    eq729_time_mem (ht10 n) (hKne n) hk
  -- the 1-loop input of Lemma 5.15, from `hP.lk 1` (the `+` 1-loops, `K̃ = m`)
  have h1 : StochDomAt (Pgue d) d.size
      (fun n (p : Fin (gueGridK d n0 n + 1) × Z2 (d.L n)) ω =>
        ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n p.1 ω))
            (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n p.1)) ⟨[true], [p.2]⟩ -
          spectralM (E n)‖)
      (fun n p _ => (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n p.1))⁻¹) := by
    intro τ' hτ' D hD
    filter_upwards [hP.lk 1 le_rfl (by omega) τ' hτ' D hD] with n hn
    refine le_trans (measure_mono ?_) hn
    rintro ω ⟨⟨k, a⟩, hlt⟩
    refine ⟨(k, (fun _ => true), (fun _ => a)), ?_⟩
    have hk : (k : ℕ) ≤ gueGridK d n0 n := Nat.lt_succ_iff.1 k.isLt
    have hKt := hKone n _ (hKmem n k hk) true a
    have hloop : (loopOf (fun _ : Fin 1 => true) (fun _ : Fin 1 => a) : LoopIdx (Z2 (d.L n))) =
        ⟨[true], [a]⟩ := rfl
    have hm : KLoop.mSig (E n) true = spectralM (E n) := by simp [KLoop.mSig]
    change ((d.size n : ℕ) : ℝ) ^ τ' *
        (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ 1 <
      ‖gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 (gueGridK d n0) n k ω))
          (spectralZ (E n) (gridTime t1 t0 (gueGridK d n0) n k))
            (loopOf (fun _ : Fin 1 => true) (fun _ : Fin 1 => a)) -
        Kt n (gridTime t1 t0 (gueGridK d n0) n k)
          (loopOf (fun _ : Fin 1 => true) (fun _ : Fin 1 => a))‖
    rw [hloop, hKt, hm, pow_one]
    exact hlt
  have hX := gueGrid_expect_oneLoop d hκ hsize hE ht1 ht10 ht0 hKne h1 τ hτ
  have hKb := Eq729B_K_bounds d hκ hτU hsize hE ht1 ht10 ht0 h730 hell Kt hKinit
    (fun n t ht I hI h2 h3 => hK n t ht I hI (by omega) (by omega)) τ hτ
  have hb1 := hP.lk 1 le_rfl (by omega) τ hτ 12 (by norm_num)
  have hb2 := hP.lk 2 (by norm_num) (by omega) τ hτ 12 (by norm_num)
  have hb3 := hP.lk 3 (by norm_num) hn0 τ hτ 12 (by norm_num)
  have hin := hB τ hτ
  filter_upwards [h730, hscale, hell, hKb, hX, hb1, hb2, hb3, hin,
    hsize.eventually (eventually_le_rpow 56 hτ)] with n h730n hscalen hellN hKbn hXn hb1n hb2n hb3n
    hinn hN56
  intro σ₂ a b
  -- the size parameter `n`: scales
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN9 : (9 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast Eq729B_nine_le_size d n
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have ht0n0 : 0 ≤ t0 n := (ht1 n).trans (ht10 n)
  set η0 : ℝ := etaT (E n) (t0 n) with hη0
  have hη0pos : 0 < η0 := eq729_eta_pos (hE2 n) (ht0 n)
  have hη01 : η0 ≤ 1 := by
    rw [hη0]; unfold etaT
    have him : (spectralM (E n)).im ≤ 1 := by
      have := Complex.im_le_norm (spectralM (E n)); rwa [norm_spectralM (hE2 n).le] at this
    have h0 : 0 ≤ 1 - t0 n := by linarith [ht0 n]
    have h1' : 1 - t0 n ≤ 1 := by linarith
    have hm0 : 0 ≤ (spectralM (E n)).im := (spectralM_im_pos (hE2 n)).le
    calc (1 - t0 n) * (spectralM (E n)).im ≤ 1 * 1 := mul_le_mul h1' him hm0 zero_le_one
      _ = 1 := one_mul 1
  set Λ : ℝ := (gueScale d E n (t0 n))⁻¹ with hΛ
  have hΛdef : Λ = (N * η0)⁻¹ := rfl
  have hΛpos : 0 < Λ := by rw [hΛdef]; positivity
  have hΛτ : Λ ≤ N ^ (-τU) := hscalen
  have hΛ1 : Λ ≤ 1 := hΛτ.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  set ρ : ℝ := N ^ τ with hρ
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow hN1 hτ.le
  have hρ0 : 0 ≤ ρ := by linarith
  have hρτ : ρ * N ^ (-τU) ≤ 1 := by
    rw [hρ, ← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hρΛ : ρ * Λ ≤ 1 := (mul_le_mul_of_nonneg_left hΛτ hρ0).trans hρτ
  have hinvs : ∀ s ∈ Set.Icc (t1 n) (t0 n), (gueScale d E n s)⁻¹ ≤ Λ := fun s hs =>
    Eq729B_inv_scale_le d (hE2 n) hs.2 (ht0 n)
  have hinvs0 : ∀ s ∈ Set.Icc (t1 n) (t0 n), 0 ≤ (gueScale d E n s)⁻¹ := fun s hs =>
    (inv_pos.2 (Eq729B_gueScale_pos d (hE2 n) (lt_of_le_of_lt hs.2 (ht0 n)))).le
  have hinvsn : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ m : ℕ, (gueScale d E n s)⁻¹ ^ m ≤ Λ ^ m :=
    fun s hs m => pow_le_pow_left₀ (hinvs0 s hs) (hinvs s hs) m
  -- `K̃` on 2- and 3-loops
  have hK2b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ := fun s hs s1 s2 x y =>
    ((hKbn s hs).1 s1 s2 x y).trans (mul_le_mul_of_nonneg_left (hinvs s hs) hρ0)
  have hK3b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w,
      ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2 := fun s hs s1 s2 s3 x y w =>
    ((hKbn s hs).2 s1 s2 s3 x y w).trans (mul_le_mul_of_nonneg_left (hinvsn s hs 2) hρ0)
  have hKd : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
        (primRhsGUE (d.L n) (d.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩)
        (Set.Icc (t1 n) (t0 n)) s := fun s hs s1 s2 x y =>
    hK n s hs _ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega)
  -- Lemma 5.15 at the grid times
  have hX' : ∀ k < gueGridK d n0 n, ∀ a,
      ‖(∫ ω, eq729F d t1 t0 (gueGridK d n0) E n k ω ⟨[true], [a]⟩ ∂(Pgue d)) - spectralM (E n)‖
        ≤ ρ * Λ ^ 2 := by
    intro k hk a
    have := hXn (⟨k, by omega⟩, a)
    exact this.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem n k hk.le) 2) hρ0)
  -- the bad event
  set B : Set (PathΩ d) := Eq729B_Bad d E t1 t0 Kt n0 1 τ n ∪ Eq729B_Bad d E t1 t0 Kt n0 2 τ n
    ∪ Eq729B_Bad d E t1 t0 Kt n0 3 τ n with hBdef
  have hNrpow : N ^ (-(12 : ℝ)) = 1 / N ^ 12 := by
    rw [Real.rpow_neg hN0.le, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      one_div]
  have hBm : Pgue d B ≤ ENNReal.ofReal (3 / N ^ 12) := by
    have hb1' : Pgue d (Eq729B_Bad d E t1 t0 Kt n0 1 τ n) ≤ ENNReal.ofReal (N ^ (-(12 : ℝ))) := hb1n
    have hb2' : Pgue d (Eq729B_Bad d E t1 t0 Kt n0 2 τ n) ≤ ENNReal.ofReal (N ^ (-(12 : ℝ))) := hb2n
    have hb3' : Pgue d (Eq729B_Bad d E t1 t0 Kt n0 3 τ n) ≤ ENNReal.ofReal (N ^ (-(12 : ℝ))) := hb3n
    have h12 : Pgue d (Eq729B_Bad d E t1 t0 Kt n0 1 τ n ∪ Eq729B_Bad d E t1 t0 Kt n0 2 τ n)
        ≤ Pgue d (Eq729B_Bad d E t1 t0 Kt n0 1 τ n) + Pgue d (Eq729B_Bad d E t1 t0 Kt n0 2 τ n) :=
      measure_union_le _ _
    have h123 : Pgue d B ≤ Pgue d (Eq729B_Bad d E t1 t0 Kt n0 1 τ n ∪ Eq729B_Bad d E t1 t0 Kt n0 2 τ n)
        + Pgue d (Eq729B_Bad d E t1 t0 Kt n0 3 τ n) := measure_union_le _ _
    refine (h123.trans (add_le_add h12 le_rfl)).trans ?_
    refine (add_le_add (add_le_add hb1' hb2') hb3').trans (le_of_eq ?_)
    rw [hNrpow, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  have hg1 : ∀ ω ∉ B, ∀ k < gueGridK d n0 n, ∀ σ a,
      ‖eq729F d t1 t0 (gueGridK d n0) E n k ω ⟨[σ], [a]⟩ - KLoop.mSig (E n) σ‖ ≤ ρ * Λ := by
    intro ω hω k hk σ a
    have hω1 : ω ∉ Eq729B_Bad d E t1 t0 Kt n0 1 τ n := fun h => hω (Or.inl (Or.inl h))
    have h : ‖eq729F d t1 t0 (gueGridK d n0) E n k ω ⟨[σ], [a]⟩
        - Kt n (gridTime t1 t0 (gueGridK d n0) n k) ⟨[σ], [a]⟩‖
        ≤ N ^ τ * (gueScale d E n (gridTime t1 t0 (gueGridK d n0) n k))⁻¹ ^ 1 :=
      Eq729B_not_bad d hω1 hk.le (fun _ => σ) (fun _ => a)
    rw [hKone n _ (hKmem n k hk.le) σ a] at h
    refine h.trans ?_
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left (hinvs _ (hKmem n k hk.le)) hρ0
  have hg2 : ∀ ω ∉ B, ∀ k < gueGridK d n0 n, ∀ s1 s2 x y,
      ‖eq729F d t1 t0 (gueGridK d n0) E n k ω ⟨[s1, s2], [x, y]⟩
        - Kt n (gridTime t1 t0 (gueGridK d n0) n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2 := by
    intro ω hω k hk s1 s2 x y
    have hω2 : ω ∉ Eq729B_Bad d E t1 t0 Kt n0 2 τ n := fun h => hω (Or.inl (Or.inr h))
    have h := Eq729B_not_bad d hω2 hk.le ![s1, s2] ![x, y]
    exact h.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem n k hk.le) 2) hρ0)
  have hg3 : ∀ ω ∉ B, ∀ k < gueGridK d n0 n, ∀ s1 s2 s3 x y w,
      ‖eq729F d t1 t0 (gueGridK d n0) E n k ω ⟨[s1, s2, s3], [x, y, w]⟩
        - Kt n (gridTime t1 t0 (gueGridK d n0) n k) ⟨[s1, s2, s3], [x, y, w]⟩‖
          ≤ ρ * Λ ^ 3 := by
    intro ω hω k hk s1 s2 s3 x y w
    have hω3 : ω ∉ Eq729B_Bad d E t1 t0 Kt n0 3 τ n := fun h => hω (Or.inr h)
    have h := Eq729B_not_bad d hω3 hk.le ![s1, s2, s3] ![x, y, w]
    exact h.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem n k hk.le) 3) hρ0)
  -- the initial term, from `MLExpConcl d E t1`
  have ht1mem : t1 n ∈ Set.Icc (t1 n) (t0 n) := ⟨le_rfl, ht10 n⟩
  have ht1lt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hinit : ∀ s1 s2 x y,
      ‖eq729e d t1 t0 (gueGridK d n0) E Kt n 0 ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 3 := by
    intro s1 s2 x y
    have he : eq729e d t1 t0 (gueGridK d n0) E Kt n 0 ⟨[s1, s2], [x, y]⟩
        = RBM.Evol.expLoopErr d n (E n) (t1 n) ![s1, s2] ![x, y] := by
      unfold eq729e eq729F RBM.Evol.expLoopErr
      rw [GoodEvent_gridTime_zero, hKinit,
        Eq729B_transfer d t1 t0 (gueGridK d n0) n (ht1 n) (spectralZ (E n) (t1 n))]
      rfl
    have h := hinn ![s1, s2] ![x, y]
    have hsc : scaleM (d.L n) (d.W n) (E n) (t1 n) = gueScale d E n (t1 n) := by
      unfold scaleM gueScale
      rw [ellT_eq_L ht1lt hellN, Sizes.size_eq]
      push_cast
      ring
    rw [he]
    refine h.trans ?_
    rw [hsc, ← inv_pow]
    exact mul_le_mul_of_nonneg_left (hinvsn _ ht1mem 3) hρ0
  -- `N Δ ≤ 1`
  have hKge : N + 1 ≤ (gueGridK d n0 n : ℝ) := by
    unfold gueGridK; push_cast
    exact le_self_pow₀ (by linarith) (by omega)
  have hKpos : (0 : ℝ) < (gueGridK d n0 n : ℝ) := by linarith
  have hE0 : 0 ≤ t0 n - t1 n := by linarith [ht10 n]
  have hE01 : t0 n - t1 n ≤ 1 := by linarith [ht1 n, ht0 n]
  have hMΔ : N * gridStep t1 t0 (gueGridK d n0) n ≤ 1 := by
    unfold gridStep
    rw [mul_div_assoc']
    rw [div_le_one hKpos]
    nlinarith
  -- the one-size bound at `n`
  have hper := Eq729B_perN d (gueGridK d n0) Kt (hE2 n) (ht1 n) (ht10 n) (ht0 n) (hKne n)
    (Λ := Λ) (ρ := ρ) (p := 3 / N ^ 12) (B0 := ρ * Λ ^ 3) hΛdef hΛ1
    hρ0 hρΛ (by positivity) hMΔ hK2b hK3b hKd hX' hBm hg1 hg2 hg3 hinit true σ₂ a b
  have hΛN : 1 ≤ N * Λ := by
    rw [hΛdef, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    calc N * η0 ≤ N * 1 := mul_le_mul_of_nonneg_left hη01 hN0.le
      _ = N := mul_one _
  have hθ : (t0 n - t1 n) * N * Λ * ρ ≤ 1 := by
    have h1 : (t0 n - t1 n) * N * Λ = (t0 n - t1 n) / η0 := by
      rw [hΛdef]; field_simp
    have h2 : (t0 n - t1 n) / η0 ≤ N ^ (-τU) := by
      rw [div_le_iff₀ hη0pos]; exact h730n
    rw [h1]
    calc (t0 n - t1 n) / η0 * ρ ≤ N ^ (-τU) * ρ :=
          mul_le_mul_of_nonneg_right h2 hρ0
      _ = ρ * N ^ (-τU) := mul_comm _ _
      _ ≤ 1 := hρτ
  have hKr : ((gueGridK d n0 n : ℕ) : ℝ) = (N + 1) ^ (2 * (16 * n0 + 32)) := by
    rw [show 2 * (16 * n0 + 32) = 32 * n0 + 64 by ring]
    unfold gueGridK; push_cast; rfl
  have harith := Eq729B_arith (N := d.size n) (Eq729B_nine_le_size d n) (ρ := ρ) (Λ := Λ)
    (E0 := t0 n - t1 n) (Δ := gridStep t1 t0 (gueGridK d n0) n) (Kr := (gueGridK d n0 n : ℝ))
    (16 * n0 + 32) (by omega) hKr hρ1 hΛpos hΛN hE01 (eq729_KΔ (hKne n))
    (eq729_step_nonneg (ht10 n)) hθ
  -- `56 N^τ ≤ N^δ`
  have hW : 56 * ρ ≤ N ^ δ := by
    calc 56 * ρ ≤ N ^ τ * N ^ τ := mul_le_mul_of_nonneg_right hN56 hρ0
      _ = N ^ (τ + τ) := (Real.rpow_add hN0 _ _).symm
      _ ≤ N ^ δ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- the left side is `e_K`
  have hlhs : (∫ ω, gloop (d.L n) (d.W n)
          (blockMat (gueH d t1 t0 (gueGridK d n0) n (gueGridK d n0 n) ω))
          (spectralZ (E n) (t0 n)) ⟨[true, σ₂], [a, b]⟩ ∂(Pgue d)) -
      kTwoGUE (d.L n) (d.W n) (KLoop.mSig (E n)) (t1 n) (t0 n) true σ₂ a b
      = eq729e d t1 t0 (gueGridK d n0) E Kt n (gueGridK d n0 n) ⟨[true, σ₂], [a, b]⟩ := by
    unfold eq729e eq729F
    rw [gridTime_last t1 t0 (gueGridK d n0) n (hKne n),
      hK2 n (t0 n) ⟨ht10 n, le_rfl⟩ true σ₂ a b]
  rw [hlhs]
  calc ‖eq729e d t1 t0 (gueGridK d n0) E Kt n (gueGridK d n0 n) ⟨[true, σ₂], [a, b]⟩‖
      ≤ 56 * ρ * Λ ^ 3 := hper.trans harith
    _ ≤ N ^ δ * Λ ^ 3 := mul_le_mul_of_nonneg_right hW (by positivity)

/-! ### The (7.47) step, part 1: the law (7.26) and the main term -/

section Eq747

/-- `tr(G E_a G^{(σ)} E_b)` of a Hermitian matrix is the `(+, σ)` 2-loop of its block matrix. -/
private theorem Eq729B_trGEGEmat_eq_gloop (L W : ℕ) [NeZero L] [NeZero W]
    (M : Matrix (Idx L W) (Idx L W) ℂ) (hM : M.IsHermitian) (z : ℂ) (σ : Bool) (a b : Z2 L) :
    trGEGEmat L W M z σ a b = gloop L W (blockMat M) z ⟨[true, σ], [a, b]⟩ := by
  have hGσ : (if σ then green M z else (green M z)ᴴ) = Gsig M z σ := by
    cases σ
    · have h := Gsig_conjTranspose hM z true
      simp only [Bool.not_true] at h
      simpa using h
    · simp
  rw [gloop_two, RBM.Endpoints.ZRescale_gsig_block, RBM.Endpoints.ZRescale_gsig_block,
    ← RBM.Endpoints.ZRescale_blockMat_Epaper a, ← RBM.Endpoints.ZRescale_blockMat_Epaper b,
    ← RBM.Endpoints.ZRescale_blockMat_mul, ← RBM.Endpoints.ZRescale_blockMat_mul,
    ← RBM.Endpoints.ZRescale_blockMat_mul, RBM.Endpoints.ZRescale_trace_block]
  unfold trGEGEmat
  rw [hGσ]
  simp only [Gsig_true, Matrix.mul_assoc]

/-- `z_{t₀}^{(E')} = √t₀ z` for `(E', t₀) = (lemE z, lemT z)` (`eq:zztE`; the private
`GUEPhaseGrid_spectralZ_eq` of `Grid.lean`). -/
private theorem Eq729B_spectralZ_eq {z : ℂ} (hz : 0 < z.im) :
    spectralZ (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z := by
  have hu := RBM.Endpoints.ZRescale_lemT_pos hz
  have hs : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
  have h := eq_inv_sqrt_mul_spectralZ hz
  calc spectralZ (lemE z) (lemT z)
      = (Real.sqrt (lemT z) : ℂ) *
          ((Real.sqrt (lemT z) : ℂ)⁻¹ * spectralZ (lemE z) (lemT z)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    _ = (Real.sqrt (lemT z) : ℂ) * z := by rw [← h]

/-- **The law (7.26) in expectation**: at the last grid
step, `E tr G(z) E_a G(z)^{(σ)} E_b = t₀ E L_{t₀,(+,σ),(a,b)}`, with `t₀ = lemT z`,
`t₁ = (1 - ζ(t)) t₀`
(`map_gueH_last`, `GUEPhaseGrid_gloop_two_smul_lemT_eq`). -/
private theorem Eq729B_law726 (d : Sizes) {t t0 : ℕ → ℝ} (K : ℕ → ℕ) (n : ℕ) {z : ℂ}
    (hz : 0 < z.im) (ht0 : t0 n = lemT z) (ht : 0 ≤ t n) (hK : K n ≠ 0) (σ : Bool)
    (a b : Z2 (d.L n)) :
    ∫ ω, trGEGEmat (d.L n) (d.W n) (ouMat (d.L n) (d.W n) (t n) ω) z σ a b
        ∂(ouP (d.L n) (d.W n)) =
      (lemT z : ℂ) * ∫ ω, gloop (d.L n) (d.W n)
        (blockMat (gueH d (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω))
        (spectralZ (lemE z) (lemT z)) ⟨[true, σ], [a, b]⟩ ∂(Pgue d) := by
  have ht0pos : 0 ≤ t0 n := by rw [ht0]; exact (RBM.Endpoints.ZRescale_lemT_pos hz).le
  set F : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ → ℂ := fun M =>
    gloop (d.L n) (d.W n) (blockMat M) (spectralZ (lemE z) (lemT z)) ⟨[true, σ], [a, b]⟩ with hF
  have hFm : Measurable F := GoodEvent_measurable_gloop (d.L n) (d.W n) _ _
  have hg : Measurable (fun ω : Ω (d.L n) (d.W n) × Ω (d.L n) (d.W n) =>
      ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (d.L n) (d.W n) (t n) ω) :=
    (measurable_ouMat (d.L n) (d.W n) (t n)).const_smul ((Real.sqrt (t0 n) : ℝ) : ℂ)
  have hint : ∫ ω, gloop (d.L n) (d.W n)
        (blockMat (gueH d (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω))
        (spectralZ (lemE z) (lemT z)) ⟨[true, σ], [a, b]⟩ ∂(Pgue d) =
      ∫ ω, F (((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (d.L n) (d.W n) (t n) ω)
        ∂(ouP (d.L n) (d.W n)) := by
    calc ∫ ω, gloop (d.L n) (d.W n)
          (blockMat (gueH d (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω))
          (spectralZ (lemE z) (lemT z)) ⟨[true, σ], [a, b]⟩ ∂(Pgue d)
        = ∫ M, F M ∂((Pgue d).map (gueH d (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n))) :=
          (integral_map (gueH_measurable d _ t0 K n (K n)).aemeasurable
            hFm.aestronglyMeasurable).symm
      _ = ∫ M, F M ∂((ouP (d.L n) (d.W n)).map
            (fun ω => ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (d.L n) (d.W n) (t n) ω)) := by
          rw [map_gueH_last d t0 t K n ht0pos ht hK]
      _ = ∫ ω, F (((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (d.L n) (d.W n) (t n) ω)
            ∂(ouP (d.L n) (d.W n)) :=
          integral_map hg.aemeasurable hFm.aestronglyMeasurable
  rw [hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  change trGEGEmat (d.L n) (d.W n) (ouMat (d.L n) (d.W n) (t n) ω) z σ a b =
    (lemT z : ℂ) * gloop (d.L n) (d.W n)
      (blockMat (((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (d.L n) (d.W n) (t n) ω))
      (spectralZ (lemE z) (lemT z)) ⟨[true, σ], [a, b]⟩
  have hl : (loopOf ![true, σ] ![a, b] : LoopIdx (Z2 (d.L n))) = ⟨[true, σ], [a, b]⟩ := by
    simp [loopOf, List.ofFn_succ]
  have h := GUEPhaseGrid_gloop_two_smul_lemT_eq (blockMat (ouMat (d.L n) (d.W n) (t n) ω)) hz σ a b
  rw [hl] at h
  rw [Eq729B_trGEGEmat_eq_gloop _ _ _ (ouMat_isHermitian _ _ _ _) z σ a b, h, ht0]
  rfl

/-- The main term of (7.47): `profileTilde = t₀ K̃_{t₀}` of the GUE phase at `(E', t₀) = (lemE z,
lemT z)`, `t₁ = (1 - ζ) t₀` (`lemT_mul_kTwoGUE_pp/pm`, `mSC = msc`). -/
private theorem Eq729B_profile_eq (L W : ℕ) [NeZero L] (hL : 3 ≤ L) {z : ℂ} (hz : 0 < z.im)
    {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (σ : Bool) (a b : Z2 L) :
    profileTilde L W ζ z σ a b =
      (lemT z : ℂ) * kTwoGUE L W (KLoop.mSig (lemE z)) ((1 - ζ) * lemT z) (lemT z) true σ a b := by
  have hm : RBM.Endpoints.mSC z = msc z := RBM.Endpoints.mSC_eq_msc hz
  cases σ
  · rw [lemT_mul_kTwoGUE_pm L W hL hz hζ0 hζ1 a b]
    unfold profileTilde
    simp only [hm, Bool.false_eq_true, ite_false]
    ring
  · rw [lemT_mul_kTwoGUE_pp L W hL hz hζ0 hζ1 a b]
    unfold profileTilde
    simp only [hm, ite_true]
    ring

end Eq747

/-! ### The (7.47) step, part 2: the scales at `z = E + i η_Q` -/

section Eq747Scales

private theorem Eq729B_etaQ_pos (d : Sizes) (n : ℕ) : 0 < ouEtaQ d n := by
  unfold ouEtaQ
  have hW : (0 : ℝ) < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  exact div_pos (Real.rpow_pos_of_pos hW _) (Eq729B_size_pos d n)

private theorem Eq729B_size_eq (d : Sizes) (n : ℕ) :
    ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := by
  rw [Sizes.size_eq]; push_cast; ring

private theorem Eq729B_etaQ_mul_size (d : Sizes) (n : ℕ) :
    ouEtaQ d n * ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ ((2 : ℝ) / 3) := by
  unfold ouEtaQ
  have := (Eq729B_size_pos d n).ne'
  field_simp

private theorem Eq729B_W_pow_le (d : Sizes) (n : ℕ) :
    (d.W n : ℝ) ^ ((2 : ℝ) / 3) ≤ (d.W n : ℝ) ^ 2 := by
  have hw : (1 : ℝ) ≤ d.W n := by exact_mod_cast d.W_pos n
  calc (d.W n : ℝ) ^ ((2 : ℝ) / 3) ≤ (d.W n : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hw (by norm_num)
    _ = (d.W n : ℝ) ^ 2 := by rw [Real.rpow_two]

private theorem Eq729B_etaQ_le_inv_sq (d : Sizes) (n : ℕ) :
    ouEtaQ d n ≤ ((d.L n : ℝ) ^ 2)⁻¹ := by
  have hw : (1 : ℝ) ≤ d.W n := by exact_mod_cast d.W_pos n
  have hl : (0 : ℝ) < d.L n := by exact_mod_cast (by have := d.three_le_L n; omega : 0 < d.L n)
  have hη := Eq729B_etaQ_mul_size d n
  have hN : ((d.size n : ℕ) : ℝ) = (d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2 := Eq729B_size_eq d n
  have h1 := Eq729B_W_pow_le d n
  rw [hN] at hη
  have hw2 : (0 : ℝ) < (d.W n : ℝ) ^ 2 := by positivity
  have hl2 : (0 : ℝ) < (d.L n : ℝ) ^ 2 := by positivity
  have hηL : ouEtaQ d n * (d.L n : ℝ) ^ 2 ≤ 1 := by
    have h2 : ouEtaQ d n * (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 2 ≤ 1 * (d.W n : ℝ) ^ 2 := by
      calc ouEtaQ d n * (d.L n : ℝ) ^ 2 * (d.W n : ℝ) ^ 2
          = ouEtaQ d n * ((d.W n : ℝ) ^ 2 * (d.L n : ℝ) ^ 2) := by ring
        _ ≤ 1 * (d.W n : ℝ) ^ 2 := by rw [hη, one_mul]; exact h1
    exact le_of_mul_le_mul_right h2 hw2
  rw [← one_div, le_div_iff₀ hl2]
  exact hηL

private theorem Eq729B_etaQ_le_one (d : Sizes) (n : ℕ) : ouEtaQ d n ≤ 1 := by
  have hl : (3 : ℝ) ≤ d.L n := by exact_mod_cast d.three_le_L n
  refine (Eq729B_etaQ_le_inv_sq d n).trans ?_
  rw [inv_le_one₀ (by positivity)]
  nlinarith

/-- `Meta` at `z = E + i η_Q`: `ℓ(z) = L + 1` since `η_Q^{-1/2} = W^{2/3} L ≥ L`. -/
private theorem Eq729B_meta_eq (d : Sizes) (n : ℕ) (E : ℝ) :
    Meta (d.L n) (d.W n) ((E : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) =
      (d.W n : ℝ) ^ 2 * ((d.L n : ℝ) + 1) ^ 2 * ouEtaQ d n := by
  have him : ((E : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I).im = ouEtaQ d n := by simp
  unfold Meta ellz
  rw [him]
  have hη := Eq729B_etaQ_pos d n
  have hl : (0 : ℝ) < d.L n := by exact_mod_cast (by have := d.three_le_L n; omega : 0 < d.L n)
  have hmin : min (ouEtaQ d n ^ (-(1 / 2 : ℝ))) (d.L n : ℝ) = (d.L n : ℝ) := by
    refine min_eq_right ?_
    rw [RBM.Endpoints.ZRescale_rpow_neg_half hη.le]
    have hs : 0 < Real.sqrt (ouEtaQ d n) := Real.sqrt_pos.2 hη
    rw [le_inv_comm₀ hl hs]
    calc Real.sqrt (ouEtaQ d n) ≤ Real.sqrt (((d.L n : ℝ) ^ 2)⁻¹) :=
          Real.sqrt_le_sqrt (Eq729B_etaQ_le_inv_sq d n)
      _ = (d.L n : ℝ)⁻¹ := by rw [← inv_pow, Real.sqrt_sq (by positivity)]
  rw [hmin]

/-- `N η_Q ≤ Meta ≤ (16/9) N η_Q` at `z = E + i η_Q` (`L ≥ 3`). -/
private theorem Eq729B_meta_cmp (d : Sizes) (n : ℕ) (E : ℝ) :
    ((d.size n : ℕ) : ℝ) * ouEtaQ d n ≤
        Meta (d.L n) (d.W n) ((E : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) ∧
      Meta (d.L n) (d.W n) ((E : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) ≤
        (16 / 9) * (((d.size n : ℕ) : ℝ) * ouEtaQ d n) := by
  rw [Eq729B_meta_eq, Eq729B_size_eq]
  have hl : (3 : ℝ) ≤ d.L n := by exact_mod_cast d.three_le_L n
  have hη := Eq729B_etaQ_pos d n
  have hw2 : (0 : ℝ) ≤ (d.W n : ℝ) ^ 2 := by positivity
  have h0 : 0 ≤ (d.W n : ℝ) ^ 2 * ouEtaQ d n := by positivity
  constructor
  · nlinarith [mul_nonneg h0 (by positivity : (0 : ℝ) ≤ 2 * (d.L n : ℝ) + 1)]
  · nlinarith [mul_nonneg h0 (by nlinarith : (0 : ℝ) ≤ 7 * (d.L n : ℝ) ^ 2 - 18 * (d.L n : ℝ) - 9)]

/-- `η_{t₀} = √t₀ Im z` (`eq:zztE`): `etaT (lemE z) (lemT z) = √(lemT z) · Im z`. -/
private theorem Eq729B_etaT_lemT {z : ℂ} (hz : 0 < z.im) :
    etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * z.im := by
  have h := spectralZ_im (lemE z) (lemT z)
  rw [Eq729B_spectralZ_eq hz, Complex.im_ofReal_mul] at h
  unfold etaT
  exact h.symm

private theorem Eq729B_lemT_lt_one {z : ℂ} (hz : 0 < z.im) : lemT z < 1 := by
  have := norm_msc_lt_one hz
  have := norm_nonneg (msc z)
  unfold lemT
  nlinarith

/-- `(1 - t₀) c_κ ≤ Im z` with `c_κ = √(κ(4 - κ))/2` (`Im m^{(E')} ≥ c_κ`, `(1 - t₀) Im m^{(E')} =
√t₀ Im z`; the proof of `zMeta`). -/
private theorem Eq729B_one_sub_lemT_le {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) (hre : |z.re| ≤ 2 - κ) :
    (1 - lemT z) * (Real.sqrt (κ * (4 - κ)) / 2) ≤ z.im := by
  obtain ⟨hE, hu16, -, -⟩ := zztE_quant hκ hz hz1 hre
  have hu1 := Eq729B_lemT_lt_one hz
  have hmkE : Real.sqrt (κ * (4 - κ)) / 2 ≤ (spectralM (lemE z)).im := by
    rw [spectralM_im]
    have h1 := abs_le.1 hE
    have : κ * (4 - κ) ≤ 4 - lemE z ^ 2 := by nlinarith [h1.1, h1.2]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt this) (by norm_num)
  have hid : (1 - lemT z) * (spectralM (lemE z)).im = Real.sqrt (lemT z) * z.im := by
    have := Eq729B_etaT_lemT hz
    unfold etaT at this
    exact this
  have hs1 : Real.sqrt (lemT z) ≤ 1 := Real.sqrt_le_one.2 hu1.le
  calc (1 - lemT z) * (Real.sqrt (κ * (4 - κ)) / 2)
      ≤ (1 - lemT z) * (spectralM (lemE z)).im :=
        mul_le_mul_of_nonneg_left hmkE (by linarith)
    _ = Real.sqrt (lemT z) * z.im := hid
    _ ≤ 1 * z.im := mul_le_mul_of_nonneg_right hs1 hz.le
    _ = z.im := one_mul _

/-- The scale conversion `(N η_{t₀})^{-3} = t₀^{-3/2} (N η)^{-3}` (`η_{t₀} = t₀^{1/2} η`,
(2.37)): `t₀ a (N t₀^{1/2} y)^{-3} ≤ 4 a (N y)^{-3}` for `t₀ ≥ 1/16`. -/
private theorem Eq729B_scale_747 {t0 a n y : ℝ} (ht0 : 1 / 16 ≤ t0) (ha : 0 ≤ a) (hn : 0 < n)
    (hy : 0 < y) :
    t0 * (a * (n * (Real.sqrt t0 * y))⁻¹ ^ 3) ≤ 4 * a * (n * y)⁻¹ ^ 3 := by
  have ht0' : 0 < t0 := by linarith
  set s := Real.sqrt t0 with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ht0'
  have hss : s * s = t0 := Real.mul_self_sqrt ht0'.le
  have hs4 : 1 / 4 ≤ s := by
    rw [show (1 : ℝ) / 4 = Real.sqrt (1 / 16) by
      rw [show (1 : ℝ) / 16 = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht0
  have e : t0 * (a * (n * (s * y))⁻¹ ^ 3) = s⁻¹ * (a * (n * y)⁻¹ ^ 3) := by
    rw [← hss]; field_simp
  rw [e]
  have hsi : s⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ hs0 (by norm_num)]; linarith
  have : 0 ≤ a * (n * y)⁻¹ ^ 3 := by positivity
  nlinarith

end Eq747Scales

/-! ### The (7.47) step: from (7.29) at `t₀` to the bound of `OUEq747` -/

/-- **(7.47) from (7.29) and (7.26)**.  Let `z_n = E_n + i η_Q` (`η_Q = W^{2/3}/N`),
`t₀ = lemT z_n`, `E' = lemE z_n` (Lemma 2.8, `z = t₀^{-1/2} z_{t₀}^{(E')}`), `t₁ = (1 - ζ(t_n)) t₀`.
If (7.29) holds at `t₀` on the GUE-phase grid in the loss form `N^δ (N η_{t₀})^{-3}` (`H729`), then
the one-time law (7.26) at the last step (`map_gueH_last`) and `kTwoGUE_eq_ThetaTilde` give the
bound
of `OUEq747` at `(E, t)`, with `W^δ Meta^{-3}`: `W ≥ N^𝔠` (`Admissible`) turns the loss `N^{𝔠δ/2}`
into `W^δ`, and `t₀ (N η_{t₀})^{-3} ≤ 4 (N η_Q)^{-3} ≤ 4 (16/9)^3 Meta^{-3}`. -/
theorem Eq729B_eq747_of_eq729 (d : Sizes) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hA : RBM.Endpoints.Admissible 𝔠 d) {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) {E' t0 t1 : ℕ → ℝ}
    (hE' : ∀ n, E' n = lemE ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (ht0 : ∀ n, t0 n = lemT ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (ht1 : ∀ n, t1 n = (1 - ouZeta (t n)) * t0 n) {K : ℕ → ℕ} (hK : ∀ n, K n ≠ 0)
    (H729 : ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ (σ₂ : Bool) (a b : Z2 (d.L n)),
      ‖(∫ ω, gloop (d.L n) (d.W n) (blockMat (gueH d t1 t0 K n (K n) ω))
            (spectralZ (E' n) (t0 n)) ⟨[true, σ₂], [a, b]⟩ ∂(Pgue d)) -
          kTwoGUE (d.L n) (d.W n) (KLoop.mSig (E' n)) (t1 n) (t0 n) true σ₂ a b‖ ≤
        ((d.size n : ℕ) : ℝ) ^ δ * (gueScale d E' n (t0 n))⁻¹ ^ 3) :
    ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ (σ : Bool) (a b : Z2 (d.L n)),
      ‖(∫ ω, trGEGEmat (d.L n) (d.W n) (ouMat (d.L n) (d.W n) (t n) ω)
            ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b ∂(ouP (d.L n) (d.W n))) -
          profileTilde (d.L n) (d.W n) (ouZeta (t n))
            ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b‖ ≤
        (d.W n : ℝ) ^ δ * (Meta (d.L n) (d.W n)
          ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))⁻¹ ^ 3 := by
  intro δ hδ
  have hδ' : 0 < 𝔠 * δ / 2 := by have := mul_pos h𝔠 hδ; linarith
  have ht1fun : t1 = fun n => (1 - ouZeta (t n)) * t0 n := funext ht1
  subst ht1fun
  filter_upwards [H729 (𝔠 * δ / 2) hδ', hA.2, hA.1.eventually (eventually_le_rpow 23 hδ')]
    with n hH hNW h23
  intro σ a b
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := Eq729B_size_pos d n
  set z : ℂ := (E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I with hzdef
  have hzim : z.im = ouEtaQ d n := by simp [hzdef]
  have hzre : z.re = E n := by simp [hzdef]
  have hη := Eq729B_etaQ_pos d n
  have hz : 0 < z.im := by rw [hzim]; exact hη
  have hz1 : z.im ≤ 1 := by rw [hzim]; exact Eq729B_etaQ_le_one d n
  have hzκ : |z.re| ≤ 2 - κ := by rw [hzre]; exact hE n
  obtain ⟨-, hu16, -, -⟩ := zztE_quant hκ hz hz1 hzκ
  have hζ0 : 0 ≤ ouZeta (t n) := ZeroModeProfile_ouZeta_nonneg (ht n)
  have hζ1 : ouZeta (t n) ≤ 1 := ZeroModeProfile_ouZeta_le_one _
  have hu0 : 0 ≤ lemT z := by linarith
  have hE'n : E' n = lemE z := hE' n
  have ht0n : t0 n = lemT z := ht0 n
  -- (7.26) and the main term
  have e1 : (∫ ω, trGEGEmat (d.L n) (d.W n) (ouMat (d.L n) (d.W n) (t n) ω) z σ a b
        ∂(ouP (d.L n) (d.W n))) - profileTilde (d.L n) (d.W n) (ouZeta (t n)) z σ a b
      = (lemT z : ℂ) * ((∫ ω, gloop (d.L n) (d.W n)
          (blockMat (gueH d (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω))
          (spectralZ (lemE z) (lemT z)) ⟨[true, σ], [a, b]⟩ ∂(Pgue d)) -
        kTwoGUE (d.L n) (d.W n) (KLoop.mSig (lemE z)) ((1 - ouZeta (t n)) * lemT z) (lemT z)
          true σ a b) := by
    rw [Eq729B_law726 d K n hz ht0n (ht n) (hK n) σ a b,
      Eq729B_profile_eq (d.L n) (d.W n) (d.three_le_L n) hz hζ0 hζ1 σ a b, mul_sub]
  have hsc : gueScale d E' n (t0 n) = N * (Real.sqrt (lemT z) * ouEtaQ d n) := by
    unfold gueScale
    rw [hE'n, ht0n, Eq729B_etaT_lemT hz, hzim]
  have hH2 := hH σ a b
  rw [hsc] at hH2
  rw [hE'n, ht0n] at hH2
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  -- the scales
  obtain ⟨hm1, hm2⟩ := Eq729B_meta_cmp d n (E n)
  have hMpos : 0 < Meta (d.L n) (d.W n) z := lt_of_lt_of_le (mul_pos hN0 hη) hm1
  have hinv : (N * ouEtaQ d n)⁻¹ ≤ (16 / 9) * (Meta (d.L n) (d.W n) z)⁻¹ := by
    have h1 : (16 / 9 * (N * ouEtaQ d n))⁻¹ ≤ (Meta (d.L n) (d.W n) z)⁻¹ :=
      inv_anti₀ hMpos hm2
    have e : (N * ouEtaQ d n)⁻¹ = (16 / 9) * (16 / 9 * (N * ouEtaQ d n))⁻¹ := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hWδ : N ^ (𝔠 * δ) ≤ (d.W n : ℝ) ^ δ := by
    calc N ^ (𝔠 * δ) = (N ^ 𝔠) ^ δ := Real.rpow_mul hN0.le _ _
      _ ≤ (d.W n : ℝ) ^ δ := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hNW hδ.le
  have hNN : N ^ (𝔠 * δ / 2) * N ^ (𝔠 * δ / 2) = N ^ (𝔠 * δ) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hNδ0 : 0 ≤ N ^ (𝔠 * δ / 2) := Real.rpow_nonneg hN0.le _
  have hMinv0 : 0 ≤ (Meta (d.L n) (d.W n) z)⁻¹ := inv_nonneg.2 hMpos.le
  calc lemT z * ‖(∫ ω, gloop (d.L n) (d.W n)
          (blockMat (gueH d (fun n => (1 - ouZeta (t n)) * t0 n) t0 K n (K n) ω))
          (spectralZ (lemE z) (lemT z)) ⟨[true, σ], [a, b]⟩ ∂(Pgue d)) -
        kTwoGUE (d.L n) (d.W n) (KLoop.mSig (lemE z)) ((1 - ouZeta (t n)) * lemT z) (lemT z)
          true σ a b‖
      ≤ lemT z * (N ^ (𝔠 * δ / 2) * (N * (Real.sqrt (lemT z) * ouEtaQ d n))⁻¹ ^ 3) :=
        mul_le_mul_of_nonneg_left hH2 hu0
    _ ≤ 4 * N ^ (𝔠 * δ / 2) * (N * ouEtaQ d n)⁻¹ ^ 3 :=
        Eq729B_scale_747 hu16 hNδ0 hN0 hη
    _ ≤ 4 * N ^ (𝔠 * δ / 2) * ((16 / 9) * (Meta (d.L n) (d.W n) z)⁻¹) ^ 3 := by
        gcongr
    _ = (4 * (16 / 9) ^ 3) * N ^ (𝔠 * δ / 2) * (Meta (d.L n) (d.W n) z)⁻¹ ^ 3 := by ring
    _ ≤ 23 * N ^ (𝔠 * δ / 2) * (Meta (d.L n) (d.W n) z)⁻¹ ^ 3 := by
        gcongr; norm_num
    _ ≤ N ^ (𝔠 * δ / 2) * N ^ (𝔠 * δ / 2) * (Meta (d.L n) (d.W n) z)⁻¹ ^ 3 := by
        gcongr
    _ = N ^ (𝔠 * δ) * (Meta (d.L n) (d.W n) z)⁻¹ ^ 3 := by rw [hNN]
    _ ≤ (d.W n : ℝ) ^ δ * (Meta (d.L n) (d.W n) z)⁻¹ ^ 3 := by gcongr

/-! ### The (7.47) step: the hypotheses of `gueGrid_eq729` at `(E', t₁, t₀)` -/

section Eq747Derived

/-- The deterministic facts at every `n`: `|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1`. -/
private theorem Eq729B_pw (d : Sizes) {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) {E' t0 t1 : ℕ → ℝ}
    (hE' : ∀ n, E' n = lemE ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (ht0 : ∀ n, t0 n = lemT ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (ht1 : ∀ n, t1 n = (1 - ouZeta (t n)) * t0 n) (n : ℕ) :
    |E' n| ≤ 2 - κ ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1 := by
  set z : ℂ := (E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I with hzdef
  have hzim : z.im = ouEtaQ d n := by simp [hzdef]
  have hzre : z.re = E n := by simp [hzdef]
  have hz : 0 < z.im := by rw [hzim]; exact Eq729B_etaQ_pos d n
  have hz1 : z.im ≤ 1 := by rw [hzim]; exact Eq729B_etaQ_le_one d n
  have hzκ : |z.re| ≤ 2 - κ := by rw [hzre]; exact hE n
  obtain ⟨hE2, hu16, -, -⟩ := zztE_quant hκ hz hz1 hzκ
  have hu1 := Eq729B_lemT_lt_one hz
  have hζ0 : 0 ≤ ouZeta (t n) := ZeroModeProfile_ouZeta_nonneg (ht n)
  have hζ1 : ouZeta (t n) ≤ 1 := ZeroModeProfile_ouZeta_le_one _
  have ht0n : t0 n = lemT z := ht0 n
  have hu0 : 0 ≤ t0 n := by rw [ht0n]; linarith
  refine ⟨by rw [hE' n]; exact hE2, ?_, ?_, by rw [ht0n]; exact hu1⟩
  · rw [ht1 n]; exact mul_nonneg (by linarith) hu0
  · rw [ht1 n]; nlinarith

/-- Claim A of the exponent table: `4 N^{2 τ_U} ≤ W^{2/3}` for `τ_U ≤ 𝔠/12`, `W ≥ N^𝔠` and
`4 ≤ N^{𝔠/2}`. -/
private theorem Eq729B_claimA (d : Sizes) {𝔠 τU : ℝ} (hτUm : τU ≤ 𝔠 / 12) (n : ℕ)
    (hNW : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ))
    (h4 : 4 ≤ ((d.size n : ℕ) : ℝ) ^ (𝔠 / 2)) :
    4 * ((d.size n : ℕ) : ℝ) ^ (2 * τU) ≤ (d.W n : ℝ) ^ ((2 : ℝ) / 3) := by
  have hN9 : (9 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast Eq729B_nine_le_size d n
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set w : ℝ := (d.W n : ℝ) with hw
  have h1 : N ^ (2 * τU) ≤ N ^ (𝔠 / 6) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h2' : (N ^ 𝔠) ^ ((2 : ℝ) / 3) ≤ w ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hNW (by norm_num)
  have h3 : (N ^ 𝔠) ^ ((2 : ℝ) / 3) = N ^ (𝔠 / 2) * N ^ (𝔠 / 6) := by
    rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]; congr 1; ring
  have h5 : 0 ≤ N ^ (𝔠 / 6) := Real.rpow_nonneg hN0.le _
  calc 4 * N ^ (2 * τU) ≤ 4 * N ^ (𝔠 / 6) := by gcongr
    _ ≤ N ^ (𝔠 / 2) * N ^ (𝔠 / 6) := by gcongr
    _ = (N ^ 𝔠) ^ ((2 : ℝ) / 3) := h3.symm
    _ ≤ w ^ ((2 : ℝ) / 3) := h2'

/-- `t*_n = N^{-1+τ_U} ≤ η_Q/4` (from Claim A, `η_Q N = W^{2/3}`). -/
private theorem Eq729B_Ntau_le_etaQ (d : Sizes) {𝔠 τU : ℝ} (hτU : 0 < τU) (hτUm : τU ≤ 𝔠 / 12)
    (n : ℕ) (hNW : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ))
    (h4 : 4 ≤ ((d.size n : ℕ) : ℝ) ^ (𝔠 / 2)) :
    ((d.size n : ℕ) : ℝ) ^ (-1 + τU) ≤ ouEtaQ d n / 4 := by
  have hN9 : (9 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by exact_mod_cast Eq729B_nine_le_size d n
  have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < ((d.size n : ℕ) : ℝ) := by linarith
  have hA4 := Eq729B_claimA d hτUm n hNW h4
  have hηN := Eq729B_etaQ_mul_size d n
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  set η : ℝ := ouEtaQ d n with hηdef
  have hN2 : N ^ (2 * τU) ≤ η / 4 * N := by nlinarith [hA4, hηN]
  have hNτ : N ^ τU ≤ N ^ (2 * τU) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have e : N ^ (-1 + τU) = N ^ τU / N := by
    rw [Real.rpow_add hN0, Real.rpow_neg_one, div_eq_mul_inv, mul_comm]
  rw [e, div_le_iff₀ hN0]
  linarith

/-- **The three asymptotic hypotheses of `gueGrid_eq729` at size `n`**, from the sizes at the QUE
scale `η_Q = W^{2/3}/N` (`W ≥ N^𝔠`, `t ≤ N^{-1+τ_U}`, `τ_U ≤ 𝔠/12`): `h730`, `hscale`, `hell`.  The
size conditions are the three
`N^𝔠 ≤ W`, `4 ≤ N^{𝔠/2}`, `2/c_κ ≤ N^𝔠`. -/
private theorem Eq729B_good_pw (d : Sizes) {𝔠 κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτUm : τU ≤ 𝔠 / 12) (n : ℕ) {E t : ℝ} (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τU))
    (hNW : ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ))
    (h4 : 4 ≤ ((d.size n : ℕ) : ℝ) ^ (𝔠 / 2))
    (h2 : 2 / (Real.sqrt (κ * (4 - κ)) / 2) ≤ ((d.size n : ℕ) : ℝ) ^ 𝔠)
    {z : ℂ} (hzdef : z = (E : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) :
    lemT z - (1 - ouZeta t) * lemT z ≤
        ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (lemE z) (lemT z) ∧
      (((d.size n : ℕ) : ℝ) * etaT (lemE z) (lemT z))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) ∧
      (d.L n : ℝ) ^ 2 * (1 - (1 - ouZeta t) * lemT z) ≤ 1 := by
  set N : ℝ := ((d.size n : ℕ) : ℝ) with hNdef
  have hN9 : (9 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast Eq729B_nine_le_size d n
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  set w : ℝ := (d.W n : ℝ) with hw
  have hw1 : 1 ≤ w := by rw [hw]; exact_mod_cast d.W_pos n
  have hw0 : 0 < w := by linarith
  have hηpos := Eq729B_etaQ_pos d n
  set η : ℝ := ouEtaQ d n with hηdef
  have hηN : η * N = w ^ ((2 : ℝ) / 3) := Eq729B_etaQ_mul_size d n
  have hηL : η ≤ ((d.L n : ℝ) ^ 2)⁻¹ := Eq729B_etaQ_le_inv_sq d n
  have hzim : z.im = η := by rw [hzdef]; simp
  have hzre : z.re = E := by rw [hzdef]; simp
  have hz : 0 < z.im := by rw [hzim]; exact hηpos
  have hz1 : z.im ≤ 1 := by rw [hzim]; exact Eq729B_etaQ_le_one d n
  have hzκ : |z.re| ≤ 2 - κ := by rw [hzre]; exact hE
  obtain ⟨-, hu16, -, -⟩ := zztE_quant hκ hz hz1 hzκ
  have hu1 := Eq729B_lemT_lt_one hz
  have hs1 : Real.sqrt (lemT z) ≤ 1 := Real.sqrt_le_one.2 hu1.le
  have hs4 : 1 / 4 ≤ Real.sqrt (lemT z) := by
    rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hu16
  have hetaT : etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * η := by
    rw [Eq729B_etaT_lemT hz, hzim]
  -- Claim A: `4 N^{2 τ_U} ≤ W^{2/3}`
  have hA4 : 4 * N ^ (2 * τU) ≤ w ^ ((2 : ℝ) / 3) := Eq729B_claimA d hτUm n hNW h4
  have hwle : w ^ ((2 : ℝ) / 3) ≤ w := by
    calc w ^ ((2 : ℝ) / 3) ≤ w ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
      _ = w := Real.rpow_one w
  have hN2 : N ^ (2 * τU) ≤ η / 4 * N := by nlinarith [hA4, hηN]
  have hNτ : N ^ τU ≤ N ^ (2 * τU) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hN1τ : N ^ (-1 + τU) ≤ η / 4 := Eq729B_Ntau_le_etaQ d hτU hτUm n hNW h4
  refine ⟨?_, ?_, ?_⟩
  · -- h730
    have hζ0 : 0 ≤ ouZeta t := ZeroModeProfile_ouZeta_nonneg ht0
    have hζt : ouZeta t ≤ t := ZeroModeProfile_ouZeta_le t
    have hdiff : lemT z - (1 - ouZeta t) * lemT z = ouZeta t * lemT z := by ring
    have hd1 : ouZeta t * lemT z ≤ N ^ (-1 + τU) :=
      calc ouZeta t * lemT z ≤ ouZeta t * 1 := mul_le_mul_of_nonneg_left hu1.le hζ0
        _ = ouZeta t := mul_one _
        _ ≤ t := hζt
        _ ≤ N ^ (-1 + τU) := ht1
    have e1 : N ^ (-τU) * (N ^ (2 * τU) / N) = N ^ (-1 + τU) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one N, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hlow : N ^ (-1 + τU) ≤ N ^ (-τU) * etaT (lemE z) (lemT z) := by
      rw [← e1, hetaT]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _)
      rw [div_le_iff₀ hN0]
      nlinarith [hN2, mul_le_mul_of_nonneg_right hs4 (by positivity : (0 : ℝ) ≤ η * N)]
    rw [hdiff]
    exact hd1.trans hlow
  · -- hscale
    have hprod : N ^ τU ≤ N * etaT (lemE z) (lemT z) := by
      rw [hetaT]
      have : N * (Real.sqrt (lemT z) * η) = Real.sqrt (lemT z) * (η * N) := by ring
      rw [this, hηN]
      nlinarith [mul_le_mul_of_nonneg_right hs4 (Real.rpow_nonneg hw0.le ((2 : ℝ) / 3))]
    rw [Real.rpow_neg hN0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hprod
  · -- hell
    have hl : (3 : ℝ) ≤ d.L n := by exact_mod_cast d.three_le_L n
    have hl2 : (0 : ℝ) < (d.L n : ℝ) ^ 2 := by positivity
    have hηL2 : η * (d.L n : ℝ) ^ 2 ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hηL hl2.le
      rwa [inv_mul_cancel₀ hl2.ne'] at this
    have hηLw : η * (d.L n : ℝ) ^ 2 * w ≤ 1 := by
      have hN' : N = w ^ 2 * (d.L n : ℝ) ^ 2 := Eq729B_size_eq d n
      have h1 : η * (d.L n : ℝ) ^ 2 * w * w ≤ 1 * w := by
        calc η * (d.L n : ℝ) ^ 2 * w * w = η * N := by rw [hN']; ring
          _ = w ^ ((2 : ℝ) / 3) := hηN
          _ ≤ 1 * w := by rw [one_mul]; exact hwle
      exact le_of_mul_le_mul_right h1 hw0
    have hmk0 : 0 < Real.sqrt (κ * (4 - κ)) / 2 := by
      have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
      have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
      positivity
    set mk : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hmk
    have hwmk : 2 ≤ mk * w := by
      have h3 : 2 / mk ≤ w := h2.trans hNW
      rw [div_le_iff₀ hmk0] at h3
      linarith
    have hone := Eq729B_one_sub_lemT_le hκ hz hz1 hzκ
    rw [hzim] at hone
    have hX : (d.L n : ℝ) ^ 2 * (1 - lemT z) ≤ 1 / 2 := by
      have hX0 : 0 ≤ (d.L n : ℝ) ^ 2 * (1 - lemT z) := mul_nonneg hl2.le (by linarith)
      have h1 : (d.L n : ℝ) ^ 2 * (1 - lemT z) * mk ≤ (d.L n : ℝ) ^ 2 * η := by
        calc (d.L n : ℝ) ^ 2 * (1 - lemT z) * mk = (d.L n : ℝ) ^ 2 * ((1 - lemT z) * mk) := by ring
          _ ≤ (d.L n : ℝ) ^ 2 * η := mul_le_mul_of_nonneg_left hone hl2.le
      have h2'' : (d.L n : ℝ) ^ 2 * (1 - lemT z) * (mk * w) ≤ 1 := by
        calc (d.L n : ℝ) ^ 2 * (1 - lemT z) * (mk * w)
            = ((d.L n : ℝ) ^ 2 * (1 - lemT z) * mk) * w := by ring
          _ ≤ ((d.L n : ℝ) ^ 2 * η) * w := mul_le_mul_of_nonneg_right h1 hw0.le
          _ = η * (d.L n : ℝ) ^ 2 * w := by ring
          _ ≤ 1 := hηLw
      have h3 := mul_le_mul_of_nonneg_left hwmk hX0
      linarith only [h3, h2'']
    have hζ0 : 0 ≤ ouZeta t := ZeroModeProfile_ouZeta_nonneg ht0
    have hζt : ouZeta t ≤ t := ZeroModeProfile_ouZeta_le t
    have hY : (d.L n : ℝ) ^ 2 * (ouZeta t * lemT z) ≤ 1 / 4 := by
      have h1 : ouZeta t * lemT z ≤ η / 4 :=
        calc ouZeta t * lemT z ≤ ouZeta t * 1 := mul_le_mul_of_nonneg_left hu1.le hζ0
          _ = ouZeta t := mul_one _
          _ ≤ t := hζt
          _ ≤ N ^ (-1 + τU) := ht1
          _ ≤ η / 4 := hN1τ
      calc (d.L n : ℝ) ^ 2 * (ouZeta t * lemT z) ≤ (d.L n : ℝ) ^ 2 * (η / 4) :=
            mul_le_mul_of_nonneg_left h1 hl2.le
        _ = (η * (d.L n : ℝ) ^ 2) / 4 := by ring
        _ ≤ 1 / 4 := by linarith
    have e : (d.L n : ℝ) ^ 2 * (1 - (1 - ouZeta t) * lemT z)
        = (d.L n : ℝ) ^ 2 * (1 - lemT z) + (d.L n : ℝ) ^ 2 * (ouZeta t * lemT z) := by ring
    rw [e]
    linarith

end Eq747Derived

section Eq747Derived2

/-- The three eventual hypotheses of `gueGrid_eq729` at `(E', t₁, t₀)`: `h730`, `hscale`, `hell`. -/
private theorem Eq729B_derived (d : Sizes) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hA : RBM.Endpoints.Admissible 𝔠 d) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτUm : τU ≤ ouTauMax 𝔠) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ)
    (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar d τU n) {E' t0 t1 : ℕ → ℝ}
    (hE' : ∀ n, E' n = lemE ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (ht0 : ∀ n, t0 n = lemT ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (ht1 : ∀ n, t1 n = (1 - ouZeta (t n)) * t0 n) :
    (∀ᶠ n in atTop, t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E' n) (t0 n)) ∧
      (∀ᶠ n in atTop, (gueScale d E' n (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU)) ∧
      (∀ᶠ n in atTop, (d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1) := by
  have hτ12 : τU ≤ 𝔠 / 12 := hτUm.trans (min_le_left _ _)
  have hκ2 : κ ≤ 2 := by have := abs_nonneg (E 0); have := hE 0; linarith
  have hmk0 : 0 < Real.sqrt (κ * (4 - κ)) / 2 := by
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    positivity
  have hev : ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ) ∧
      4 ≤ ((d.size n : ℕ) : ℝ) ^ (𝔠 / 2) ∧
      2 / (Real.sqrt (κ * (4 - κ)) / 2) ≤ ((d.size n : ℕ) : ℝ) ^ 𝔠 := by
    filter_upwards [hA.2, hA.1.eventually (eventually_le_rpow 4 (by positivity : 0 < 𝔠 / 2)),
      hA.1.eventually (eventually_le_rpow (2 / (Real.sqrt (κ * (4 - κ)) / 2)) h𝔠)]
      with n h1 h2 h3 using ⟨h1, h2, h3⟩
  have hgood : ∀ᶠ n in atTop,
      (t0 n - t1 n ≤ ((d.size n : ℕ) : ℝ) ^ (-τU) * etaT (E' n) (t0 n)) ∧
      ((gueScale d E' n (t0 n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ^ (-τU)) ∧
      ((d.L n : ℝ) ^ 2 * (1 - t1 n) ≤ 1) := by
    filter_upwards [hev] with n hn
    obtain ⟨h1, h2, h3⟩ := hn
    have hz := Eq729B_good_pw d hκ hτU hτ12 n (hE n) (ht n).1 (ht n).2 h1 h2 h3
      (z := (E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) rfl
    rw [← ht0 n, ← hE' n] at hz
    obtain ⟨hz1, hz2, hz3⟩ := hz
    refine ⟨?_, ?_, ?_⟩
    · rw [ht1 n]; exact hz1
    · exact hz2
    · rw [ht1 n]; exact hz3
  exact ⟨hgood.mono fun n hn => hn.1, hgood.mono fun n hn => hn.2.1,
    hgood.mono fun n hn => hn.2.2⟩

/-- **(7.47) from the inputs of `gueGrid_eq729`**: at `(E', t₁, t₀)`, `E' = lemE z_n`,
`t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀`, `z_n = E_n + i η_Q`, `0 ≤ t_n ≤ t*_n = N^{-1+τ_U}`,
`τ_U ≤ τ₀(𝔠)`, `W ≥ N^𝔠`: the hypotheses `h730`, `hscale`, `hell`, `Tendsto size`,
`|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1` of `gueGrid_eq729` are derived (Lemma 2.8, `zztE_quant`), and
`gueGrid_eq729` at `δ' = 𝔠δ/2` followed by `Eq729B_eq747_of_eq729` is the bound of `OUEq747` at
`(E, t)`.  The remaining inputs are those of `gueGrid_eq729`: `K̃` (`hKinit`, `hK`, `hK2`),
`MLExpConcl d E' t₁` (`ML:exp` at `t₁`) and `GUEPathBounds` ((7.28) on the grid). -/
theorem Eq729B_eq747_of_inputs (d : Sizes) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hA : RBM.Endpoints.Admissible 𝔠 d) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτUm : τU ≤ ouTauMax 𝔠) (n0 : ℕ) (hn0 : 3 ≤ n0) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar d τU n) {E' t0 t1 : ℕ → ℝ}
    (hE' : ∀ n, E' n = lemE ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (ht0 : ∀ n, t0 n = lemT ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))
    (ht1 : ∀ n, t1 n = (1 - ouZeta (t n)) * t0 n)
    (Kt : ∀ n, ℝ → LoopIdx (Z2 (d.L n)) → ℂ)
    (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (d.L n) (d.W n) (E' n) (t1 n) I)
    (hK : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Z2 (d.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE (d.L n) (d.W n) (Kt n s) I)
        (Set.Icc (t1 n) (t0 n)) s)
    (hK2 : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Z2 (d.L n)),
      Kt n s ⟨[σ₁, σ₂], [a, b]⟩ =
        kTwoGUE (d.L n) (d.W n) (KLoop.mSig (E' n)) (t1 n) s σ₁ σ₂ a b)
    (hB : RBM.Evol.MLExpConcl d E' t1) (hP : GUEPathBounds d E' t1 t0 (gueGridK d n0) n0 Kt) :
    ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ (σ : Bool) (a b : Z2 (d.L n)),
      ‖(∫ ω, trGEGEmat (d.L n) (d.W n) (ouMat (d.L n) (d.W n) (t n) ω)
            ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b ∂(ouP (d.L n) (d.W n))) -
          profileTilde (d.L n) (d.W n) (ouZeta (t n))
            ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I) σ a b‖ ≤
        (d.W n : ℝ) ^ δ * (Meta (d.L n) (d.W n)
          ((E n : ℂ) + ((ouEtaQ d n : ℝ) : ℂ) * Complex.I))⁻¹ ^ 3 := by
  have hpw := Eq729B_pw d hκ hE (fun n => (ht n).1) hE' ht0 ht1
  obtain ⟨h730, hscale, hell⟩ := Eq729B_derived d h𝔠 hA hκ hτU hτUm hE ht hE' ht0 ht1
  have key := gueGrid_eq729 d hκ hτU n0 hn0 hA.1 (fun n => (hpw n).1) (fun n => (hpw n).2.1)
    (fun n => (hpw n).2.2.1) (fun n => (hpw n).2.2.2) h730 hscale hell Kt hKinit hK hK2 hB hP
  exact Eq729B_eq747_of_eq729 d h𝔠 hA hκ hE (fun n => (ht n).1) hE' ht0 ht1
    (K := gueGridK d n0) (gueGridK_ne_zero d n0) key

end Eq747Derived2

end RBM.Univ.GUEPhase

end
