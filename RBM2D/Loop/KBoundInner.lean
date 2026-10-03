/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Loop.KBoundEmpty
import RBM2D.Loop.LatticeCount
import RBM2D.Loop.PropHyp

/-!
# The inner sum `Σ_u |A(u)| ≺ X_t^{k-2}` by localisation

Theorems (namespace `RBM.KLoop`):

* `innerId_crude_prec` : a crude bound on `A(u)` (conditional on `Prop5Hyp κ c`);
* `innerId_sum_prec` : the inner-sum bound (conditional on `Prop5Hyp κ c`, `Prop6Hyp κ`).

The proof of `innerId_sum_prec` goes through the deterministic ball/complement split
`localize_of_counts` and `S10b_holds`/`innerSum_of_pins`, with their helpers, as `private`
declarations.  The inputs
are `card_ball_le`, `sum_inv_sq_le`, `sum_exp_le`, `zdist2_le`, `innerId`, `Xt`,
`innerId_eq_sum`, `one_le_Xt`, `Xt_nonneg`, `Kpi_empty_spwow3At_prec` and
`SigmaPi_empty_shortRange_prec`.  The localisation is specific to `d = 2` (the one-dimensional `ℓ¹`
argument is not used).
-/

namespace RBM.KLoop

open Finset

/-! ## 1. Definitions (private) -/

/-- The localisation radius `R = ℓ_t N^{τ'}`. -/
private noncomputable def Rloc (L : ℕ) [NeZero L] (t : ℝ) (N : ℕ) (τ' : ℝ) : ℝ :=
  ellT L t * (N : ℝ) ^ τ'

section Pins

/-- **`(spwow3)` at a general erased index `p`**, stated for
the inner molecule: for `k ≥ 3`, `σ'_p ≠ σ'_{p+1}`,
`|A(u)| ≺ X^{k-2} Σ_{j ≠ p} (|a'_j - u|² + 1)⁻¹ + X^{k-1} η_t`, `X = (ℓ_t² η_t)⁻¹`.
-/
private def spwow3At_pin : Prop :=
  ∀ (k : ℕ) [NeZero k], 3 ≤ k → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c → Prop6Hyp κ →
    UnifDetDom
      (U := fun N => (p : Par κ N) × {q : (Fin k → Bool) × Fin k // q.1 q.2 ≠ q.1 (q.2 + 1)} ×
        (Fin k → Z2 p.L) × Z2 p.L)
      (fun _ u => ‖innerId u.1.L (mSig u.1.E) u.1.t u.2.1.1.1 u.2.2.1 u.2.1.1.2 u.2.2.2‖)
      (fun _ u => Xt u.1.L u.1.E u.1.t ^ (k - 2) *
          ∑ j ∈ Finset.univ.erase u.2.1.1.2,
            ((zdist2 u.1.L (u.2.2.1 j - u.2.2.2) : ℝ) ^ 2 + 1)⁻¹
        + Xt u.1.L u.1.E u.1.t ^ (k - 1) * etaT u.1.E u.1.t)

/-- **The crude bound on `A`** (every `σ'`, every `p`): each boundary edge is
`≺ c_κ⁻¹ X e^{-c √c_κ |x| / ℓ_t}` (`Prop5Hyp`), `Σ^{(∅)} ≺ e^{-(c√c_κ/2) maxDist}`
(`SigmaPi_empty_shortRange_prec`), hence `|A(u)| ≺ X^{k-1} Σ_{j ≠ p} e^{-ε |a'_j - u| / ℓ_t}` with
`ε = c √c_κ / (8 (k - 1))`. -/
private def innerCrude_pin : Prop :=
  ∀ (k : ℕ) [NeZero k], 3 ≤ k → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c →
    UnifDetDom
      (U := fun N => (p : Par κ N) × (Fin k → Bool) × Fin k × (Fin k → Z2 p.L) × Z2 p.L)
      (fun _ u => ‖innerId u.1.L (mSig u.1.E) u.1.t u.2.1 u.2.2.2.1 u.2.2.1 u.2.2.2.2‖)
      (fun _ u => Xt u.1.L u.1.E u.1.t ^ (k - 1) *
          ∑ j ∈ Finset.univ.erase u.2.2.1,
            Real.exp (-(c * Real.sqrt (gapK κ) / (8 * ((k : ℝ) - 1))) *
              (zdist2 u.1.L (u.2.2.2.1 j - u.2.2.2.2) : ℝ) / ellT u.1.L u.1.t))

/-- **The localised estimate**: `Σ_{u ∈ Z_L²} |A(u)| ≺ (ℓ_t² η_t)^{-(k-2)}` for `k ≥ 3` and a
long root leaf `σ'_p ≠ σ'_{p+1}`. -/
private def innerSum_pin : Prop :=
  ∀ (k : ℕ) [NeZero k], 3 ≤ k → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c → Prop6Hyp κ →
    UnifDetDom
      (U := fun N => (p : Par κ N) × {q : (Fin k → Bool) × Fin k // q.1 q.2 ≠ q.1 (q.2 + 1)} ×
        (Fin k → Z2 p.L))
      (fun _ u => ∑ x : Z2 u.1.L,
        ‖innerId u.1.L (mSig u.1.E) u.1.t u.2.1.1.1 u.2.2 u.2.1.1.2 x‖)
      (fun _ u => Xt u.1.L u.1.E u.1.t ^ (k - 2))

/-- **Ball count** on `Z_L²` with the periodic `L¹` distance: `#{u : |a - u|_L ≤ R} ≤ (2R+1)²`. -/
private def card_ball_pin : Prop :=
  ∀ (L : ℕ) [NeZero L] (a : Z2 L) (R : ℝ), 0 ≤ R →
    (((Finset.univ.filter fun u : Z2 L => (zdist2 L (a - u) : ℝ) ≤ R).card : ℕ) : ℝ)
      ≤ (2 * R + 1) ^ 2

/-- **The logarithmic sum**: `Σ_{u ∈ Z_L²} (|a - u|_L² + 1)⁻¹ ≤ 5 + 4 log L` (at most `4r` points
at distance `r ≥ 1`, and `|·|_L ≤ L`). -/
private def sum_inv_sq_pin : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ a : Z2 L,
    ∑ u : Z2 L, ((zdist2 L (a - u) : ℝ) ^ 2 + 1)⁻¹ ≤ 5 + 4 * Real.log L

/-- **The localisation lemma** (deterministic).  If `F(u)` obeys the `(spwow3)`-type bound with
factor `P` and the crude bound with factor `Q`, then for every radius `R ≥ 0`
`Σ_u F(u) ≤ P X^{k-2} (k-1)(5 + 4 log L) + P X^{k-1} η (k-1)(2R+1)²
  + [R < L] Q X^{k-1} (k-1) e^{-εR/ℓ} L²`
(the ball `{u : ∃ j ≠ p, |a_j - u|_L ≤ R}` takes the first bound, its complement the second;
the complement is empty when `R ≥ L` because `|·|_L ≤ L`). -/
private def localize_pin : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (k : ℕ) [NeZero k], 3 ≤ k →
    ∀ (a : Fin k → Z2 L) (p : Fin k) (F : Z2 L → ℝ) (P Q X η ℓ ε R : ℝ),
      0 ≤ P → 0 ≤ Q → 0 ≤ X → 0 ≤ η → 0 < ℓ → 0 ≤ ε → 0 ≤ R →
      (∀ u, F u ≤ P * (X ^ (k - 2) * ∑ j ∈ Finset.univ.erase p,
          ((zdist2 L (a j - u) : ℝ) ^ 2 + 1)⁻¹ + X ^ (k - 1) * η)) →
      (∀ u, F u ≤ Q * (X ^ (k - 1) * ∑ j ∈ Finset.univ.erase p,
          Real.exp (-ε * (zdist2 L (a j - u) : ℝ) / ℓ))) →
      ∑ u, F u ≤ P * X ^ (k - 2) * (((k : ℝ) - 1) * (5 + 4 * Real.log L))
        + P * X ^ (k - 1) * η * (((k : ℝ) - 1) * (2 * R + 1) ^ 2)
        + (if (L : ℝ) ≤ R then 0
            else Q * X ^ (k - 1) * ((k : ℝ) - 1) * Real.exp (-ε * R / ℓ) * (L : ℝ) ^ 2)


/-- **The localisation step**: the localisation argument (`spwow3At` inside the ball, the crude
bound outside, `localize_pin`) gives the inner sums (proved below, `S10b_holds`). -/
private def S10b_pin : Prop :=
  spwow3At_pin → innerCrude_pin → localize_pin → innerSum_pin

end Pins

/-! ## 2. Auxiliary helpers (private) -/

section Proofs

variable (L : ℕ) [NeZero L]

/-! ### Scales: the regime `ℓ_t < L` -/

private theorem norm_one_sub_ofReal {t : ℝ} (ht1 : t < 1) : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]

private theorem ellT_eq {t : ℝ} (ht1 : t < 1) : ellT L t = min (Real.sqrt (1 - t))⁻¹ (L : ℝ) := by
  rw [ellT, ellhat, kappa, norm_one_sub_ofReal ht1]

/-- `ℓ_t ≥ 1`. -/
private theorem one_le_ellT (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 1 ≤ ellT L t := by
  rw [ellT_eq L ht1]
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  have hs1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  refine le_min ((one_le_inv₀ hs0).2 hs1) ?_
  have : (3 : ℝ) ≤ L := by exact_mod_cast hL
  linarith

/-- In the regime `ℓ_t < L`: `ℓ_t² = (1 - t)⁻¹`. -/
private theorem ellT_sq_of_lt {t : ℝ} (ht1 : t < 1) (h : ellT L t < L) :
    ellT L t ^ 2 = (1 - t)⁻¹ := by
  rw [ellT_eq L ht1] at h ⊢
  have hlt : (Real.sqrt (1 - t))⁻¹ < (L : ℝ) := by
    rcases min_lt_iff.1 h with h' | h'
    · exact h'
    · exact absurd h' (lt_irrefl _)
  rw [min_eq_left hlt.le, inv_pow, Real.sq_sqrt (by linarith)]

private theorem etaT_eq (E t : ℝ) : etaT E t = (1 - t) * (Gauss.spectralM E).im := by
  rw [etaT, Gauss.spectralZ_im]

private theorem spectralM_im_le_one (E : ℝ) : (Gauss.spectralM E).im ≤ 1 := by
  rw [Gauss.spectralM_im]
  have : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
  linarith

private theorem spectralM_im_ge {κ E : ℝ} (hE : |E| ≤ 2 - κ) :
    Real.sqrt (κ * (4 - κ)) / 2 ≤ (Gauss.spectralM E).im := by
  rw [Gauss.spectralM_im]
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hE0 hE 2
  have : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

/-- **The regime fact behind the gap**: if `ℓ_t < L` then `ℓ_t² η_t = Im m`. -/
private theorem ellT_sq_mul_etaT_of_lt {E t : ℝ} (ht1 : t < 1) (h : ellT L t < L) :
    ellT L t ^ 2 * etaT E t = (Gauss.spectralM E).im := by
  rw [ellT_sq_of_lt L ht1 h, etaT_eq]
  have : (1 : ℝ) - t ≠ 0 := by linarith
  field_simp

/-- In the regime `ℓ_t < L`: `X_t ≤ 2 / √(κ(4 - κ))`. -/
private theorem Xt_le_of_ellT_lt {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht1 : t < 1)
    (h : ellT L t < L) : Xt L E t ≤ 2 / Real.sqrt (κ * (4 - κ)) := by
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hpos : 0 < Real.sqrt (κ * (4 - κ)) := Real.sqrt_pos.2 (by nlinarith)
  rw [Xt, ellT_sq_mul_etaT_of_lt L ht1 h]
  have hge := spectralM_im_ge hE
  rw [show 2 / Real.sqrt (κ * (4 - κ)) = (Real.sqrt (κ * (4 - κ)) / 2)⁻¹ by
    rw [inv_div]]
  exact inv_anti₀ (by positivity) hge

/-- **The ball term** with `R = ℓ_t N^{τ'}`:
`X^{k-1} η_t (2R + 1)² ≤ 9 N^{2τ'} X^{k-2}` (uses `X η_t ℓ_t² = 1` and `R ≥ 1`). -/
private theorem ball_term_le (hL : 3 ≤ L) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {k N : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N) {τ' : ℝ} (hτ' : 0 ≤ τ') :
    Xt L E t ^ (k - 1) * etaT E t * (2 * Rloc L t N τ' + 1) ^ 2
      ≤ 9 * ((N : ℝ) ^ τ') ^ 2 * Xt L E t ^ (k - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hk1 : j + 2 - 1 = j + 1 := by omega
  have hk2 : j + 2 - 2 = j := by omega
  rw [hk1, hk2, pow_succ]
  set ℓ := ellT L t with hℓ
  set s := (N : ℝ) ^ τ' with hs
  set η := etaT E t with hη
  have hℓ1 : 1 ≤ ℓ := one_le_ellT L hL ht0 ht1
  have hs1 : 1 ≤ s := Real.one_le_rpow (by exact_mod_cast hN) hτ'
  have hηpos : 0 < η := by
    rw [hη, etaT_eq]
    have := Gauss.spectralM_im_pos hE
    have : 0 < 1 - t := by linarith
    positivity
  have hX : Xt L E t * η * ℓ ^ 2 = 1 := by
    rw [Xt, ← hℓ, ← hη]
    field_simp
  have hX0 : 0 ≤ Xt L E t := by rw [Xt]; positivity
  have hR : Rloc L t N τ' = ℓ * s := rfl
  rw [hR]
  have hb : (2 * (ℓ * s) + 1) ^ 2 ≤ 9 * ℓ ^ 2 * s ^ 2 := by
    have : 1 ≤ ℓ * s := by nlinarith
    nlinarith
  calc Xt L E t ^ j * Xt L E t * η * (2 * (ℓ * s) + 1) ^ 2
      ≤ Xt L E t ^ j * Xt L E t * η * (9 * ℓ ^ 2 * s ^ 2) := by gcongr
    _ = 9 * s ^ 2 * Xt L E t ^ j * (Xt L E t * η * ℓ ^ 2) := by ring
    _ = 9 * s ^ 2 * Xt L E t ^ j := by rw [hX, mul_one]

/-- **The localisation lemma holds, given the two lattice counts** (`card_ball_pin`,
`sum_inv_sq_pin`): the ball/complement split of `localize_pin` is proved here. -/
private theorem localize_of_counts (hball : card_ball_pin) (hlog : sum_inv_sq_pin) :
    localize_pin := by
  intro L _ hL k _ hk a p F P Q X η ℓ ε R hP hQ hX hη hℓ hε hR h1 h2
  classical
  set ball : Finset (Z2 L) := Finset.univ.filter fun u =>
    ∃ j ∈ Finset.univ.erase p, (zdist2 L (a j - u) : ℝ) ≤ R with hball_def
  have hcardE : (((Finset.univ.erase p).card : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ k := by omega
    push_cast [Nat.cast_sub this]
    ring
  -- the first term, summed over all of `Z_L²`
  have hS1 : ∑ u : Z2 L, ∑ j ∈ Finset.univ.erase p, ((zdist2 L (a j - u) : ℝ) ^ 2 + 1)⁻¹
      ≤ ((k : ℝ) - 1) * (5 + 4 * Real.log L) := by
    rw [Finset.sum_comm]
    calc ∑ j ∈ Finset.univ.erase p, ∑ u : Z2 L, ((zdist2 L (a j - u) : ℝ) ^ 2 + 1)⁻¹
        ≤ ∑ _j ∈ Finset.univ.erase p, (5 + 4 * Real.log L) :=
          Finset.sum_le_sum fun j _ => hlog L hL (a j)
      _ = ((k : ℝ) - 1) * (5 + 4 * Real.log L) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardE]
  -- the ball count
  have hcard : ((ball.card : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (2 * R + 1) ^ 2 := by
    have hsub : ball ⊆ (Finset.univ.erase p).biUnion fun j =>
        Finset.univ.filter fun u : Z2 L => (zdist2 L (a j - u) : ℝ) ≤ R := by
      intro u hu
      obtain ⟨j, hj, hju⟩ := (Finset.mem_filter.1 hu).2
      exact Finset.mem_biUnion.2 ⟨j, hj, Finset.mem_filter.2 ⟨Finset.mem_univ _, hju⟩⟩
    calc ((ball.card : ℕ) : ℝ)
        ≤ (((Finset.univ.erase p).biUnion fun j =>
            Finset.univ.filter fun u : Z2 L => (zdist2 L (a j - u) : ℝ) ≤ R).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ j ∈ Finset.univ.erase p,
            (((Finset.univ.filter fun u : Z2 L => (zdist2 L (a j - u) : ℝ) ≤ R).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.univ.erase p, (2 * R + 1) ^ 2 :=
          Finset.sum_le_sum fun j _ => hball L (a j) R hR
      _ = ((k : ℝ) - 1) * (2 * R + 1) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardE]
  -- inside the ball
  have hin : ∑ u ∈ ball, F u
      ≤ P * X ^ (k - 2) * (((k : ℝ) - 1) * (5 + 4 * Real.log L))
        + P * X ^ (k - 1) * η * (((k : ℝ) - 1) * (2 * R + 1) ^ 2) := by
    have hS1nn : ∀ u, 0 ≤ ∑ j ∈ Finset.univ.erase p, ((zdist2 L (a j - u) : ℝ) ^ 2 + 1)⁻¹ :=
      fun u => Finset.sum_nonneg fun j _ => by positivity
    calc ∑ u ∈ ball, F u
        ≤ ∑ u ∈ ball, P * (X ^ (k - 2) * ∑ j ∈ Finset.univ.erase p,
            ((zdist2 L (a j - u) : ℝ) ^ 2 + 1)⁻¹ + X ^ (k - 1) * η) :=
          Finset.sum_le_sum fun u _ => h1 u
      _ = P * X ^ (k - 2) * ∑ u ∈ ball, ∑ j ∈ Finset.univ.erase p,
            ((zdist2 L (a j - u) : ℝ) ^ 2 + 1)⁻¹
          + P * X ^ (k - 1) * η * ((ball.card : ℕ) : ℝ) := by
          rw [Finset.sum_congr rfl fun u _ => mul_add P _ _, Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun u _ => by ring
          · rw [Finset.sum_const, nsmul_eq_mul]
            ring
      _ ≤ P * X ^ (k - 2) * (((k : ℝ) - 1) * (5 + 4 * Real.log L))
          + P * X ^ (k - 1) * η * (((k : ℝ) - 1) * (2 * R + 1) ^ 2) := by
          gcongr
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ball)
            fun u _ _ => hS1nn u).trans hS1
  -- outside the ball
  have hout : ∑ u ∈ Finset.univ.filter (fun u => u ∉ ball), F u
      ≤ (if (L : ℝ) ≤ R then 0
          else Q * X ^ (k - 1) * ((k : ℝ) - 1) * Real.exp (-ε * R / ℓ) * (L : ℝ) ^ 2) := by
    have hpt : ∀ u ∈ Finset.univ.filter (fun u => u ∉ ball),
        F u ≤ Q * X ^ (k - 1) * ((k : ℝ) - 1) * Real.exp (-ε * R / ℓ) := by
      intro u hu
      have hnb : u ∉ ball := (Finset.mem_filter.1 hu).2
      have hfar : ∀ j ∈ Finset.univ.erase p, R < (zdist2 L (a j - u) : ℝ) := by
        intro j hj
        by_contra hle
        exact hnb (Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hj, not_lt.1 hle⟩)
      have hexp : ∀ j ∈ Finset.univ.erase p,
          Real.exp (-ε * (zdist2 L (a j - u) : ℝ) / ℓ) ≤ Real.exp (-ε * R / ℓ) := by
        intro j hj
        refine Real.exp_le_exp.2 ?_
        have := hfar j hj
        rw [div_le_div_iff_of_pos_right hℓ]
        nlinarith
      calc F u ≤ Q * (X ^ (k - 1) * ∑ j ∈ Finset.univ.erase p,
            Real.exp (-ε * (zdist2 L (a j - u) : ℝ) / ℓ)) := h2 u
        _ ≤ Q * (X ^ (k - 1) * ∑ _j ∈ Finset.univ.erase p, Real.exp (-ε * R / ℓ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hexp)
            (pow_nonneg hX _)) hQ
        _ = Q * X ^ (k - 1) * ((k : ℝ) - 1) * Real.exp (-ε * R / ℓ) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardE]; ring
    split_ifs with hLR
    · -- `R ≥ L`: every point is in the ball
      have hemp : Finset.univ.filter (fun u => u ∉ ball) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun u _ => ?_
        simp only [not_not]
        have hpk : (Finset.univ.erase p).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ p),
            Finset.card_univ, Fintype.card_fin]
          omega
        obtain ⟨j, hj⟩ := hpk
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hj, ?_⟩
        have := zdist2_le L (a j - u)
        have h' : (zdist2 L (a j - u) : ℝ) ≤ L := by exact_mod_cast this
        linarith
      rw [hemp, Finset.sum_empty]
    · calc ∑ u ∈ Finset.univ.filter (fun u => u ∉ ball), F u
          ≤ ∑ _u ∈ Finset.univ.filter (fun u => u ∉ ball),
              Q * X ^ (k - 1) * ((k : ℝ) - 1) * Real.exp (-ε * R / ℓ) :=
            Finset.sum_le_sum hpt
        _ = (((Finset.univ.filter (fun u => u ∉ ball)).card : ℕ) : ℝ) *
              (Q * X ^ (k - 1) * ((k : ℝ) - 1) * Real.exp (-ε * R / ℓ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (L : ℝ) ^ 2 * (Q * X ^ (k - 1) * ((k : ℝ) - 1) * Real.exp (-ε * R / ℓ)) := by
            have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
              have : (3 : ℝ) ≤ k := by exact_mod_cast hk
              linarith
            gcongr
            have hc : (Finset.univ.filter (fun u => u ∉ ball)).card ≤ L ^ 2 := by
              calc _ ≤ (Finset.univ : Finset (Z2 L)).card := Finset.card_le_card
                    (Finset.filter_subset _ _)
                _ = L ^ 2 := by
                    rw [Finset.card_univ, Fintype.card_prod, ZMod.card, sq]
            exact_mod_cast hc
        _ = Q * X ^ (k - 1) * ((k : ℝ) - 1) * Real.exp (-ε * R / ℓ) * (L : ℝ) ^ 2 := by ring
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u => u ∈ ball)]
  have hfb : Finset.univ.filter (fun u => u ∈ ball) = ball := by
    ext u; simp
  rw [hfb]
  linarith [hin, hout]

/-- `L ≤ N` and `L² ≤ N` on `Par κ N`. -/
private theorem Par.L_sq_le {κ : ℝ} {N : ℕ} (p : Par κ N) : ((p.L : ℝ)) ^ 2 ≤ N := by
  have hW : 1 ≤ p.W ^ 2 := Nat.one_le_pow _ _ (by have := p.hW; omega)
  have h : p.L ^ 2 ≤ N :=
    calc p.L ^ 2 ≤ p.W ^ 2 * p.L ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
      _ = N := p.hN
  exact_mod_cast h

private theorem Par.L_le {κ : ℝ} {N : ℕ} (p : Par κ N) : (p.L : ℝ) ≤ N := by
  have h1 : (1 : ℝ) ≤ p.L := by have := p.hL; exact_mod_cast (show 1 ≤ p.L by omega)
  nlinarith [p.L_sq_le]

end Proofs

/-! ## 3. `innerId_crude_prec` -/

/-! ### The crude bound

The helpers `zdist_neg` … `thetaEdge_long`, `absorb_pow` below are private copies of the private
lemmas of the same names in `RBM2D/Loop/KBoundEmpty.lean`, which takes its section `Gap` from
`RBM2D/Loop/PureLoop.lean`; the gap bound `gap_le_norm` is the bulk gap
`c_κ ≤ |1 - t m²|`. -/

section Crude

section Dist

variable {L : ℕ} [NeZero L]

private theorem le_maxDist {n : ℕ} (d : Fin n → Z2 L) (i j : Fin n) :
    zdist2 L (d i - d j) ≤ maxDist L d :=
  Finset.le_sup (f := fun q : Fin n × Fin n => zdist2 L (d q.1 - d q.2)) (mem_univ (i, j))

end Dist

section Fiber

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `Σ_{d : d_p = u} e^{-λ maxDist(d)} ≤ ((1 + 2k/λ)²)^k`: `maxDist d ≥ |d_i - u|` for each `i`. -/
private theorem fiber_exp_le (p : Fin k) (u : Z2 L) {lam : ℝ} (hlam : 0 < lam) :
    ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        Real.exp (-(lam * (maxDist L d : ℝ)))
      ≤ ((1 + 2 / (lam / k)) ^ 2) ^ k := by
  have hk : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  set g : Z2 L → ℝ := fun x => Real.exp (-(lam / k * (zdist2 L (u - x) : ℝ))) with hg
  have hpt : ∀ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
      Real.exp (-(lam * (maxDist L d : ℝ))) ≤ ∏ i, g (d i) := by
    intro d hd
    have hdp : d p = u := (mem_filter.1 hd).2
    simp only [hg]
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    have hle : ∀ i, (zdist2 L (u - d i) : ℝ) ≤ maxDist L d := by
      intro i; rw [← hdp]; exact_mod_cast le_maxDist d p i
    have hsum : ∑ i, (lam / k * (zdist2 L (u - d i) : ℝ)) ≤ lam * maxDist L d := by
      calc ∑ i, (lam / k * (zdist2 L (u - d i) : ℝ))
          ≤ ∑ _i : Fin k, (lam / k * (maxDist L d : ℝ)) :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (by positivity)
        _ = lam * maxDist L d := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    rw [sum_neg_distrib]
    linarith
  have hg0 : ∀ x, 0 ≤ g x := fun x => (Real.exp_pos _).le
  calc _ ≤ ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u), ∏ i, g (d i) :=
        sum_le_sum hpt
    _ ≤ ∑ d : Fin k → Z2 L, ∏ i, g (d i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => prod_nonneg fun _ _ => hg0 _)
    _ = (∑ x, g x) ^ k := by
        have h := Finset.prod_univ_sum (fun _ : Fin k => (univ : Finset (Z2 L)))
          (fun _ x => g x)
        rw [Fintype.piFinset_univ] at h
        rw [← h, prod_const, card_univ, Fintype.card_fin]
    _ ≤ ((1 + 2 / (lam / k)) ^ 2) ^ k := by
        refine pow_le_pow_left₀ (sum_nonneg fun _ _ => hg0 _) ?_ k
        have := sum_exp_le L (lam / k) (by positivity) u
        simpa [hg] using this

/-- **The crude bound, deterministic form**.  If `|Σ(d)| ≤ B e^{-(β/2) maxDist d}`, every
edge is `≤ K`, and the edge `j ≠ p` is `≤ K e^{-ε |x - y| / ℓ}` with `4ε ≤ β`, `ℓ ≥ 1`, then
`|Σ_{d_p = u} Σ(d) ∏_{i ≠ p} M_i(a_i, d_i)| ≤ B K^{k-1} C e^{-ε |a_j - u| / ℓ}`: the triangle
inequality `|a_j - u| ≤ |a_j - d_j| + maxDist d` costs `e^{ε maxDist d} ≤ e^{(β/4) maxDist d}`,
and the rest `e^{-(β/4) maxDist d}` is summed over the fibre by `fiber_exp_le`. -/
private theorem crude_core (hk : 3 ≤ k) (p j : Fin k) (hj : j ≠ p) (u : Z2 L)
    (a : Fin k → Z2 L) (Sg : (Fin k → Z2 L) → ℂ) (M : Fin k → Z2 L → Z2 L → ℂ)
    {B K β ε ℓ : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hβ : 0 < β) (hε : 0 ≤ ε) (hεβ : 4 * ε ≤ β)
    (hℓ : 1 ≤ ℓ)
    (hSg : ∀ d, ‖Sg d‖ ≤ B * Real.exp (-(β / 2 * (maxDist L d : ℝ))))
    (hMj : ∀ x y, ‖M j x y‖ ≤ K * Real.exp (-ε * (zdist2 L (x - y) : ℝ) / ℓ))
    (hM : ∀ i x y, ‖M i x y‖ ≤ K) :
    ‖∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        Sg d * ∏ i ∈ univ.erase p, M i (a i) (d i)‖
      ≤ B * K ^ (k - 1) * ((1 + 2 / (β / 4 / k)) ^ 2) ^ k *
          Real.exp (-ε * (zdist2 L (a j - u) : ℝ) / ℓ) := by
  have hjS : j ∈ univ.erase p := mem_erase.2 ⟨hj, mem_univ _⟩
  have hcard : ((univ.erase p).erase j).card = k - 2 := by
    rw [card_erase_of_mem hjS, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    omega
  have hℓ0 : 0 < ℓ := by linarith
  set x : ℝ := (zdist2 L (a j - u) : ℝ) with hxdef
  set F : ℝ := Real.exp (-ε * x / ℓ) with hFdef
  have hF0 : 0 ≤ F := (Real.exp_pos _).le
  have hpt : ∀ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
      ‖Sg d * ∏ i ∈ univ.erase p, M i (a i) (d i)‖ ≤
        B * K ^ (k - 1) * F * Real.exp (-(β / 4 * (maxDist L d : ℝ))) := by
    intro d hd
    have hdp : d p = u := (mem_filter.1 hd).2
    set D : ℝ := (maxDist L d : ℝ) with hDdef
    have hD : 0 ≤ D := Nat.cast_nonneg _
    set y : ℝ := (zdist2 L (a j - d j) : ℝ) with hydef
    have htri : x ≤ y + D := by
      have h1 : zdist2 L (a j - u) ≤ zdist2 L (a j - d j) + zdist2 L (d j - d p) := by
        rw [hdp]
        have := zdist2_add_le L (a j - d j) (d j - u)
        rwa [sub_add_sub_cancel] at this
      have h2 : zdist2 L (d j - d p) ≤ maxDist L d := le_maxDist d j p
      have h3 : zdist2 L (a j - u) ≤ zdist2 L (a j - d j) + maxDist L d := by omega
      simp only [hxdef, hydef, hDdef]
      exact_mod_cast h3
    have hrest : ∏ i ∈ (univ.erase p).erase j, ‖M i (a i) (d i)‖ ≤ K ^ (k - 2) := by
      calc ∏ i ∈ (univ.erase p).erase j, ‖M i (a i) (d i)‖
          ≤ ∏ _i ∈ (univ.erase p).erase j, K :=
            prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hM i _ _
        _ = K ^ (k - 2) := by rw [prod_const, hcard]
    have hexp : Real.exp (-ε * y / ℓ) * Real.exp (-(β / 2 * D))
        ≤ F * Real.exp (-(β / 4 * D)) := by
      rw [hFdef, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have e1 : ε * x / ℓ ≤ ε * y / ℓ + ε * D := by
        have h1 : ε * x ≤ ε * y + ε * D := by nlinarith
        have h2 : ε * D / ℓ ≤ ε * D := div_le_self (mul_nonneg hε hD) hℓ
        calc ε * x / ℓ ≤ (ε * y + ε * D) / ℓ := div_le_div_of_nonneg_right h1 hℓ0.le
          _ = ε * y / ℓ + ε * D / ℓ := add_div _ _ _
          _ ≤ ε * y / ℓ + ε * D := by linarith
      have e2 : ε * D ≤ β / 4 * D := by nlinarith
      have e3 : -ε * y / ℓ = -(ε * y / ℓ) := by ring
      have e4 : -ε * x / ℓ = -(ε * x / ℓ) := by ring
      rw [e3, e4]
      linarith
    have hMj' := hMj (a j) (d j)
    rw [norm_mul, norm_prod, ← mul_prod_erase _ _ hjS]
    have hk2 : K ^ (k - 1) = K * K ^ (k - 2) := by
      rw [← pow_succ']; congr 1; omega
    calc ‖Sg d‖ * (‖M j (a j) (d j)‖ * ∏ i ∈ (univ.erase p).erase j, ‖M i (a i) (d i)‖)
        ≤ (B * Real.exp (-(β / 2 * D))) *
            ((K * Real.exp (-ε * y / ℓ)) * K ^ (k - 2)) :=
          mul_le_mul (hSg d)
            (mul_le_mul hMj' hrest (prod_nonneg fun _ _ => norm_nonneg _)
              (mul_nonneg hK (Real.exp_pos _).le))
            (mul_nonneg (norm_nonneg _) (prod_nonneg fun _ _ => norm_nonneg _))
            (mul_nonneg hB (Real.exp_pos _).le)
      _ = B * K ^ (k - 1) * (Real.exp (-ε * y / ℓ) * Real.exp (-(β / 2 * D))) := by
          rw [hk2]; ring
      _ ≤ B * K ^ (k - 1) * (F * Real.exp (-(β / 4 * D))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hB (pow_nonneg hK _))
      _ = B * K ^ (k - 1) * F * Real.exp (-(β / 4 * D)) := by ring
  have hBK : 0 ≤ B * K ^ (k - 1) * F := mul_nonneg (mul_nonneg hB (pow_nonneg hK _)) hF0
  calc ‖∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
        Sg d * ∏ i ∈ univ.erase p, M i (a i) (d i)‖
      ≤ ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
          ‖Sg d * ∏ i ∈ univ.erase p, M i (a i) (d i)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
          B * K ^ (k - 1) * F * Real.exp (-(β / 4 * (maxDist L d : ℝ))) := sum_le_sum hpt
    _ = B * K ^ (k - 1) * F * ∑ d ∈ univ.filter (fun d : Fin k → Z2 L => d p = u),
          Real.exp (-(β / 4 * (maxDist L d : ℝ))) := by rw [mul_sum]
    _ ≤ B * K ^ (k - 1) * F * ((1 + 2 / (β / 4 / k)) ^ 2) ^ k :=
        mul_le_mul_of_nonneg_left (fiber_exp_le p u (by positivity)) hBK
    _ = B * K ^ (k - 1) * ((1 + 2 / (β / 4 / k)) ^ 2) ^ k * F := by ring

end Fiber

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

/-- **The bulk gap** `c_κ ≤ |1 - t m²|` for `t ≥ 0`,
`|E| ≤ 2 - κ` (`m = m^{(E)}`). -/
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

/-- **The short-edge bound from `Prop5Hyp`**: for every `τ > 0`, eventually in `N`, all entries
of `Θ_{t m(s)²}` (`s = ±`) are at most `N^τ c_κ⁻¹ e^{-c √c_κ |x-y|_L}`. -/
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

/-- `m(s) m(s') = 1` for `s ≠ s'` (`|m| = 1`). -/
private theorem mSig_mul_ne {E : ℝ} (hE : |E| ≤ 2) {s s' : Bool} (h : s ≠ s') :
    mSig E s * mSig E s' = 1 := by
  have hm : Gauss.spectralM E * (starRingEnd ℂ) (Gauss.spectralM E) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Gauss.norm_spectralM hE]
    simp
  cases s <;> cases s' <;> simp_all [mSig, mul_comm]

/-- A long edge is `Θ_t`. -/
private theorem thetaEdge_long {L : ℕ} [NeZero L] {E t : ℝ} (hE : |E| ≤ 2) {s s' : Bool}
    (h : s ≠ s') : thetaEdge L (mSig E) t s s' = Theta L (t : ℂ) := by
  rw [thetaEdge, mSig_mul_ne hE h, mul_one]

/-- `C (N^{τ/(2m)})^m ≤ N^τ` eventually. -/
private theorem absorb_pow (m : ℕ) (hm : 0 < m) (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, C * ((N : ℝ) ^ (τ / (2 * m))) ^ m ≤ (N : ℝ) ^ τ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  filter_upwards [eventually_le_rpow C (half_pos hτ)] with N hC
  have h3 : ((N : ℝ) ^ (τ / (2 * m))) ^ m = (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    field_simp
  rw [h3]
  calc C * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = (N : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half N hτ

/-- The right side of property 5 at `ξ = t` is at most `c_κ⁻¹ X_t e^{-c √c_κ x / ℓ_t}`:
`((1 - t) ℓ_t²)⁻¹ ≤ (η_t ℓ_t²)⁻¹ = X_t`, `√c_κ ≤ 1`, `c_κ ≤ 1`. -/
private theorem long_rhs_le_exp {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E t : ℝ} (hE : |E| < 2)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {c g x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hg : 0 < g)
    (hg1 : g ≤ 1) :
    Real.exp (-(c * x) / ellhat L (t : ℂ)) / (‖(1 : ℂ) - (t : ℂ)‖ * ellhat L (t : ℂ) ^ 2)
      ≤ g⁻¹ * Xt L E t * Real.exp (-(c * Real.sqrt g * x) / ellT L t) := by
  have hℓ : 1 ≤ ellT L t := one_le_ellT L hL ht0 ht1
  have hℓ' : ellhat L (t : ℂ) = ellT L t := rfl
  rw [hℓ', norm_one_sub_ofReal ht1]
  have h1t : 0 < 1 - t := by linarith
  have him := Gauss.spectralM_im_pos hE
  have him1 := spectralM_im_le_one E
  have hη : 0 < etaT E t := by rw [etaT_eq]; positivity
  have hηle : etaT E t ≤ 1 - t := by
    rw [etaT_eq]; nlinarith
  have hℓ0 : 0 < ellT L t := by linarith
  have hsg1 : Real.sqrt g ≤ 1 := Real.sqrt_le_one.2 hg1
  have hsg0 : 0 ≤ Real.sqrt g := Real.sqrt_nonneg g
  have hexp : Real.exp (-(c * x) / ellT L t) ≤ Real.exp (-(c * Real.sqrt g * x) / ellT L t) := by
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hℓ0.le
    have : c * Real.sqrt g * x ≤ c * x := by
      have hcx : 0 ≤ c * x := mul_nonneg hc hx
      nlinarith
    linarith
  have hX : ((1 - t) * ellT L t ^ 2)⁻¹ ≤ Xt L E t := by
    rw [Xt]
    refine inv_anti₀ (mul_pos (pow_pos hℓ0 2) hη) ?_
    rw [mul_comm (1 - t)]
    exact mul_le_mul_of_nonneg_left hηle (by positivity)
  have hX0 : 0 ≤ Xt L E t := Xt_nonneg L ht1
  have hG : 1 ≤ g⁻¹ := (one_le_inv₀ hg).2 hg1
  calc Real.exp (-(c * x) / ellT L t) / ((1 - t) * ellT L t ^ 2)
      = ((1 - t) * ellT L t ^ 2)⁻¹ * Real.exp (-(c * x) / ellT L t) := by
        rw [div_eq_inv_mul]
    _ ≤ Xt L E t * Real.exp (-(c * Real.sqrt g * x) / ellT L t) :=
        mul_le_mul hX hexp (Real.exp_pos _).le hX0
    _ = 1 * Xt L E t * Real.exp (-(c * Real.sqrt g * x) / ellT L t) := by ring
    _ ≤ g⁻¹ * Xt L E t * Real.exp (-(c * Real.sqrt g * x) / ellT L t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG hX0) (Real.exp_pos _).le

/-- **Every boundary edge**: eventually, `|Θ_{t m(s) m(s')}(x, y)| ≤
N^τ c_κ⁻¹ X_t e^{-c √c_κ |x - y| / ℓ_t}` for all `s, s'` (property 5; the bulk gap for
`s = s'`). -/
private theorem edge_all {κ c : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hc : 0 < c)
    (hP : Prop5Hyp κ c) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p : Par κ N) (s s' : Bool) (x y : Z2 p.L),
      ‖thetaEdge p.L (mSig p.E) p.t s s' x y‖ ≤
        (N : ℝ) ^ τ * ((gapK κ)⁻¹ * Xt p.L p.E p.t) *
          Real.exp (-(c * Real.sqrt (gapK κ) * (zdist2 p.L (x - y) : ℝ)) / ellT p.L p.t) := by
  filter_upwards [prop5_edge hκ hc hP hτ, hP τ hτ] with N hS hL5 p s s' x y
  have hE : |p.E| < 2 := by have := p.hE; linarith
  have hg := gapK_pos hκ hκ2
  have hg1 := gapK_le_one κ
  have hNτ : 0 ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) τ
  have hX := one_le_Xt p.L p.hL hE p.ht0 p.ht1
  have hℓ : 1 ≤ ellT p.L p.t := one_le_ellT p.L p.hL p.ht0 p.ht1
  set z : ℝ := (zdist2 p.L (x - y) : ℝ) with hz
  have hz0 : 0 ≤ z := Nat.cast_nonneg _
  have hβz : 0 ≤ c * Real.sqrt (gapK κ) * z := by positivity
  by_cases h : s = s'
  · subst h
    refine (hS p s x y).trans ?_
    have he : Real.exp (-(c * Real.sqrt (gapK κ) * z))
        ≤ Real.exp (-(c * Real.sqrt (gapK κ) * z) / ellT p.L p.t) := by
      apply Real.exp_le_exp.2
      rw [neg_div, neg_le_neg_iff]
      exact div_le_self hβz hℓ
    have hG0 : 0 ≤ (gapK κ)⁻¹ := by positivity
    calc (N : ℝ) ^ τ * ((gapK κ)⁻¹ * Real.exp (-(c * Real.sqrt (gapK κ) * z)))
        = (N : ℝ) ^ τ * ((gapK κ)⁻¹ * 1) * Real.exp (-(c * Real.sqrt (gapK κ) * z)) := by ring
      _ ≤ (N : ℝ) ^ τ * ((gapK κ)⁻¹ * Xt p.L p.E p.t) *
            Real.exp (-(c * Real.sqrt (gapK κ) * z) / ellT p.L p.t) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hG0) hNτ) he
            (Real.exp_pos _).le (mul_nonneg hNτ (mul_nonneg hG0 (by linarith)))
  · rw [thetaEdge_long hE.le h]
    have hξ : xiSet p.E p.t 2 = (p.t : ℂ) := by simp [xiSet]
    have h5 := hL5 ⟨p, 2, x, y⟩
    simp only [hξ] at h5
    refine h5.trans ?_
    rw [mul_assoc ((N : ℝ) ^ τ)]
    exact mul_le_mul_of_nonneg_left
      (long_rhs_le_exp p.hL hE p.ht0 p.ht1 hc.le hz0 hg hg1) hNτ

end Crude

/-- **The crude bound on `A`**.  Each boundary edge is
`≺ c_κ⁻¹ X_t e^{-c √c_κ |x| / ℓ_t}` (`Prop5Hyp` and the bulk gap),
`Σ^{(∅)} ≺ e^{-(c √c_κ / 2) maxDist}`
(`SigmaPi_empty_shortRange_prec`), hence `|A(u)| ≺ X_t^{k-1} Σ_{j ≠ p} e^{-ε |a'_j - u| / ℓ_t}`
with `ε = c √c_κ / (8 (k - 1))`, for every `σ'` and every erased index `p`.  Conditional on
`Prop5Hyp κ c`. -/
theorem innerId_crude_prec :
  ∀ (k : ℕ) [NeZero k], 3 ≤ k → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c →
    UnifDetDom
      (U := fun N => (p : Par κ N) × (Fin k → Bool) × Fin k × (Fin k → Z2 p.L) × Z2 p.L)
      (fun _ u => ‖innerId u.1.L (mSig u.1.E) u.1.t u.2.1 u.2.2.2.1 u.2.2.1 u.2.2.2.2‖)
      (fun _ u => Xt u.1.L u.1.E u.1.t ^ (k - 1) *
          ∑ j ∈ Finset.univ.erase u.2.2.1,
            Real.exp (-(c * Real.sqrt (gapK κ) / (8 * ((k : ℝ) - 1))) *
              (zdist2 u.1.L (u.2.2.2.1 j - u.2.2.2.2) : ℝ) / ellT u.1.L u.1.t)) := by
  intro k _ hk κ c hκ hc h5 τ hτ
  by_cases hκ2 : κ ≤ 2
  swap
  · refine Filter.Eventually.of_forall fun N u => ?_
    exfalso
    have h1 := u.1.hE
    have h2 := abs_nonneg u.1.E
    have h3 := not_le.1 hκ2
    linarith
  have hg := gapK_pos hκ hκ2
  have hk0 : 0 < k := by omega
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hτ' : 0 < τ / (2 * (k : ℝ)) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk0
    positivity
  have hβ : 0 < c * Real.sqrt (gapK κ) := mul_pos hc (Real.sqrt_pos.2 hg)
  have hε0 : 0 ≤ c * Real.sqrt (gapK κ) / (8 * ((k : ℝ) - 1)) := by
    have : 0 < 8 * ((k : ℝ) - 1) := by linarith
    positivity
  have hεβ : 4 * (c * Real.sqrt (gapK κ) / (8 * ((k : ℝ) - 1))) ≤ c * Real.sqrt (gapK κ) := by
    have h8 : 0 < 8 * ((k : ℝ) - 1) := by linarith
    rw [← mul_div_assoc, div_le_iff₀ h8]
    nlinarith
  set C : ℝ := (gapK κ)⁻¹ ^ (k - 1) *
    ((1 + 2 / (c * Real.sqrt (gapK κ) / 4 / k)) ^ 2) ^ k with hC
  filter_upwards [SigmaPi_empty_shortRange_prec k hk κ c hκ hc h5 _ hτ',
    edge_all hκ hκ2 hc h5 hτ', Filter.eventually_ge_atTop 1, absorb_pow k hk0 C hτ]
    with N hS hM hN1 habs
  rintro ⟨p, σ', q, a', u⟩
  dsimp only
  rw [innerId_eq_sum]
  have hE : |p.E| < 2 := by have := p.hE; linarith
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set B : ℝ := (N : ℝ) ^ (τ / (2 * (k : ℝ))) with hBdef
  have hB : 0 ≤ B := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hX := one_le_Xt p.L p.hL hE p.ht0 p.ht1
  have hX0 : 0 ≤ Xt p.L p.E p.t := by linarith
  have hℓ : 1 ≤ ellT p.L p.t := one_le_ellT p.L p.hL p.ht0 p.ht1
  have hℓ0 : 0 < ellT p.L p.t := by linarith
  have hG0 : 0 ≤ (gapK κ)⁻¹ := by positivity
  set K : ℝ := B * ((gapK κ)⁻¹ * Xt p.L p.E p.t) with hKdef
  have hK : 0 ≤ K := by positivity
  set ε : ℝ := c * Real.sqrt (gapK κ) / (8 * ((k : ℝ) - 1)) with hεdef
  -- the edge bounds in the two forms `crude_core` needs
  have hMj : ∀ (j : Fin k) (x y : Z2 p.L),
      ‖thetaEdge p.L (mSig p.E) p.t (σ' j) (σ' (j + 1)) x y‖ ≤
        K * Real.exp (-ε * (zdist2 p.L (x - y) : ℝ) / ellT p.L p.t) := by
    intro j x y
    refine (hM p (σ' j) (σ' (j + 1)) x y).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
    apply div_le_div_of_nonneg_right _ hℓ0.le
    have hz : (0 : ℝ) ≤ (zdist2 p.L (x - y) : ℝ) := Nat.cast_nonneg _
    have : ε ≤ c * Real.sqrt (gapK κ) := by linarith
    nlinarith
  have hMall : ∀ (i : Fin k) (x y : Z2 p.L),
      ‖thetaEdge p.L (mSig p.E) p.t (σ' i) (σ' (i + 1)) x y‖ ≤ K := by
    intro i x y
    refine (hMj i x y).trans ?_
    have : Real.exp (-ε * (zdist2 p.L (x - y) : ℝ) / ellT p.L p.t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      apply div_nonpos_of_nonpos_of_nonneg _ hℓ0.le
      have hz : (0 : ℝ) ≤ (zdist2 p.L (x - y) : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc K * Real.exp (-ε * (zdist2 p.L (x - y) : ℝ) / ellT p.L p.t) ≤ K * 1 :=
          mul_le_mul_of_nonneg_left this hK
      _ = K := mul_one K
  have hSg : ∀ d : Fin k → Z2 p.L, ‖SigmaPi p.L (mSig p.E) p.t σ' ∅ d‖ ≤
      B * Real.exp (-(c * Real.sqrt (gapK κ) / 2 * (maxDist p.L d : ℝ))) :=
    fun d => hS ⟨p, σ', d⟩
  -- a vertex `j ≠ q`
  have hne : (univ.erase q).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ q), card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj⟩ := hne
  have hjq : j ≠ q := ne_of_mem_erase hj
  have hcore := crude_core hk q j hjq u a' (fun d => SigmaPi p.L (mSig p.E) p.t σ' ∅ d)
    (fun i => thetaEdge p.L (mSig p.E) p.t (σ' i) (σ' (i + 1))) hB hK hβ hε0 hεβ hℓ hSg
    (hMj j) hMall
  refine hcore.trans ?_
  have hKpow : B * K ^ (k - 1) = B ^ k * ((gapK κ)⁻¹ ^ (k - 1) * Xt p.L p.E p.t ^ (k - 1)) := by
    rw [hKdef, mul_pow, mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hsum : Real.exp (-ε * (zdist2 p.L (a' j - u) : ℝ) / ellT p.L p.t) ≤
      ∑ j ∈ univ.erase q, Real.exp (-ε * (zdist2 p.L (a' j - u) : ℝ) / ellT p.L p.t) :=
    single_le_sum (f := fun j => Real.exp (-ε * (zdist2 p.L (a' j - u) : ℝ) / ellT p.L p.t))
      (fun _ _ => (Real.exp_pos _).le) hj
  have hS0 : 0 ≤ ∑ j ∈ univ.erase q, Real.exp (-ε * (zdist2 p.L (a' j - u) : ℝ) / ellT p.L p.t) :=
    sum_nonneg fun _ _ => (Real.exp_pos _).le
  have habs' : C * B ^ k ≤ (N : ℝ) ^ τ := habs
  have hXk : 0 ≤ Xt p.L p.E p.t ^ (k - 1) := pow_nonneg hX0 _
  calc B * K ^ (k - 1) * ((1 + 2 / (c * Real.sqrt (gapK κ) / 4 / k)) ^ 2) ^ k *
        Real.exp (-ε * (zdist2 p.L (a' j - u) : ℝ) / ellT p.L p.t)
      = (C * B ^ k) * (Xt p.L p.E p.t ^ (k - 1) *
          Real.exp (-ε * (zdist2 p.L (a' j - u) : ℝ) / ellT p.L p.t)) := by
        rw [hKpow, hC]; ring
    _ ≤ (N : ℝ) ^ τ * (Xt p.L p.E p.t ^ (k - 1) *
          ∑ j ∈ univ.erase q, Real.exp (-ε * (zdist2 p.L (a' j - u) : ℝ) / ellT p.L p.t)) :=
        mul_le_mul habs' (mul_le_mul_of_nonneg_left hsum hXk)
          (mul_nonneg hXk (Real.exp_pos _).le) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-! ## 4. `innerId_sum_prec` -/

section Sum

variable (L : ℕ) [NeZero L]

/-- **The localisation argument closes.**  With `τ₁ = τ/4`, `τ' = τ/8`,
`R = ℓ_t N^{τ'}`, each of the three terms of `localize_pin` is `≤ N^τ X^{k-2} / 3` eventually:
`N^{τ/4}(k-1)(5 + 4 log L)` (`log L ≤ log N ≤ (4/τ) N^{τ/4}`), `N^{τ/4}(k-1)·9 N^{τ/4}`
(`ball_term_le`), and, only when `R < L` (then `ℓ_t < L` and `X ≤ 2/√(κ(4-κ))`),
`N^{τ/4} X_κ (k-1) e^{-ε N^{τ/8}} N → 0`. -/
private theorem S10b_holds : S10b_pin := by
  intro h3 hcr hloc k _ hk κ c hκ hc h5 h6 τ hτ
  by_cases hκ2 : 2 < κ
  · refine Filter.Eventually.of_forall fun N u => ?_
    exfalso
    have := u.1.hE
    have := abs_nonneg u.1.E
    linarith
  push Not at hκ2
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  have hgap : 0 < gapK κ := by
    unfold gapK
    exact lt_min one_pos (Real.sqrt_pos.2 (by nlinarith))
  have hε : 0 < c * Real.sqrt (gapK κ) / (8 * ((k : ℝ) - 1)) := by
    have := Real.sqrt_pos.2 hgap
    have : 0 < 8 * ((k : ℝ) - 1) := by linarith
    positivity
  set ε : ℝ := c * Real.sqrt (gapK κ) / (8 * ((k : ℝ) - 1)) with hεdef
  have hXκ : 0 < 2 / Real.sqrt (κ * (4 - κ)) := by
    have : 0 < Real.sqrt (κ * (4 - κ)) := Real.sqrt_pos.2 (by nlinarith)
    positivity
  set Xκ : ℝ := 2 / Real.sqrt (κ * (4 - κ)) with hXκdef
  have hτ4 : 0 < τ / 4 := by positivity
  have hτ8 : 0 < τ / 8 := by positivity
  -- (e3) the logarithmic term
  have e3 : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ (τ / 4) * (((k : ℝ) - 1) * (5 + 4 * Real.log N)) ≤ (N : ℝ) ^ τ / 3 := by
    filter_upwards [eventually_le_rpow (3 * (((k : ℝ) - 1) * (5 + 16 / τ))) (half_pos hτ),
      Filter.eventually_ge_atTop 1] with N hN hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hlog : Real.log N ≤ (N : ℝ) ^ (τ / 4) / (τ / 4) :=
      Real.log_le_rpow_div (by positivity) hτ4
    have hs1 : 1 ≤ (N : ℝ) ^ (τ / 4) := Real.one_le_rpow hN1' hτ4.le
    have hb : 5 + 4 * Real.log N ≤ (5 + 16 / τ) * (N : ℝ) ^ (τ / 4) := by
      have h4 : 4 * ((N : ℝ) ^ (τ / 4) / (τ / 4)) = 16 / τ * (N : ℝ) ^ (τ / 4) := by
        field_simp
        ring
      have : 0 ≤ 16 / τ := by positivity
      nlinarith
    have hsq : (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (τ / 4) = (N : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add' (Nat.cast_nonneg N) (by positivity)]
      congr 1
      ring
    have hsplit := UnifDetDom.rpow_half_mul_rpow_half N hτ
    have hN2 : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    calc (N : ℝ) ^ (τ / 4) * (((k : ℝ) - 1) * (5 + 4 * Real.log N))
        ≤ (N : ℝ) ^ (τ / 4) * (((k : ℝ) - 1) * ((5 + 16 / τ) * (N : ℝ) ^ (τ / 4))) := by
          gcongr
      _ = (((k : ℝ) - 1) * (5 + 16 / τ)) * (N : ℝ) ^ (τ / 2) := by rw [← hsq]; ring
      _ ≤ ((N : ℝ) ^ (τ / 2) / 3) * (N : ℝ) ^ (τ / 2) := by
          gcongr
          linarith
      _ = (N : ℝ) ^ τ / 3 := by rw [← hsplit]; ring
  -- (e4) the ball term
  have e4 : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ (τ / 4) * (((k : ℝ) - 1) * (9 * ((N : ℝ) ^ (τ / 8)) ^ 2)) ≤ (N : ℝ) ^ τ / 3 := by
    filter_upwards [eventually_le_rpow (27 * ((k : ℝ) - 1)) (half_pos hτ)] with N hN
    have hsq8 : ((N : ℝ) ^ (τ / 8)) ^ 2 = (N : ℝ) ^ (τ / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      push_cast
      ring
    have hsq : (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (τ / 4) = (N : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add' (Nat.cast_nonneg N) (by positivity)]
      congr 1
      ring
    have hsplit := UnifDetDom.rpow_half_mul_rpow_half N hτ
    have hN2 : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    rw [hsq8]
    calc (N : ℝ) ^ (τ / 4) * (((k : ℝ) - 1) * (9 * (N : ℝ) ^ (τ / 4)))
        = (9 * ((k : ℝ) - 1)) * (N : ℝ) ^ (τ / 2) := by rw [← hsq]; ring
      _ ≤ ((N : ℝ) ^ (τ / 2) / 3) * (N : ℝ) ^ (τ / 2) := by
          gcongr
          linarith
      _ = (N : ℝ) ^ τ / 3 := by rw [← hsplit]; ring
  -- (e5) the complement of the ball
  have e5 : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ (τ / 4) * Xκ * ((k : ℝ) - 1) * Real.exp (-ε * (N : ℝ) ^ (τ / 8)) * N
        ≤ (N : ℝ) ^ τ / 3 := by
    have hg : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (τ / 8)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hτ8).comp tendsto_natCast_atTop_atTop
    have hf := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (8 / τ + 2) ε hε).comp hg
    have hδ : 0 < 1 / (3 * (Xκ * ((k : ℝ) - 1))) := by
      have : 0 < (k : ℝ) - 1 := by linarith
      positivity
    filter_upwards [(tendsto_order.1 hf).2 _ hδ, Filter.eventually_ge_atTop 1] with N hN hN1
    simp only [Function.comp] at hN
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hpow : ((N : ℝ) ^ (τ / 8)) ^ (8 / τ + 2) = (N : ℝ) * (N : ℝ) ^ (τ / 4) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg N)]
      have : τ / 8 * (8 / τ + 2) = 1 + τ / 4 := by field_simp; ring
      rw [this, Real.rpow_add' (Nat.cast_nonneg N) (by positivity), Real.rpow_one]
    rw [hpow] at hN
    have hNτ : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
    have hk0 : 0 < (k : ℝ) - 1 := by linarith
    have hprod : 0 < Xκ * ((k : ℝ) - 1) := by positivity
    calc (N : ℝ) ^ (τ / 4) * Xκ * ((k : ℝ) - 1) * Real.exp (-ε * (N : ℝ) ^ (τ / 8)) * N
        = (Xκ * ((k : ℝ) - 1)) *
            ((N : ℝ) * (N : ℝ) ^ (τ / 4) * Real.exp (-ε * (N : ℝ) ^ (τ / 8))) := by ring
      _ ≤ (Xκ * ((k : ℝ) - 1)) * (1 / (3 * (Xκ * ((k : ℝ) - 1)))) := by
          gcongr
      _ = 1 / 3 := by field_simp
      _ ≤ (N : ℝ) ^ τ / 3 := by linarith
  filter_upwards [h3 k hk κ c hκ hc h5 h6 (τ / 4) hτ4, hcr k hk κ c hκ hc h5 (τ / 4) hτ4,
    e3, e4, e5, Filter.eventually_ge_atTop 1] with N hA hB he3 he4 he5 hN1
  rintro ⟨p, ⟨⟨σ', q⟩, hq⟩, a'⟩
  have hE2 : |p.E| < 2 := by have := p.hE; linarith
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNτ4 : 0 ≤ (N : ℝ) ^ (τ / 4) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hs1 : 1 ≤ (N : ℝ) ^ (τ / 8) := Real.one_le_rpow hN1' hτ8.le
  have hX0 : 0 ≤ Xt p.L p.E p.t := Xt_nonneg p.L p.ht1
  have hη0 : 0 ≤ etaT p.E p.t := by
    rw [etaT_eq]
    have := Gauss.spectralM_im_pos hE2
    have : 0 < 1 - p.t := by linarith [p.ht1]
    positivity
  have hℓ1 : 1 ≤ ellT p.L p.t := one_le_ellT p.L p.hL p.ht0 p.ht1
  have hR0 : 0 ≤ Rloc p.L p.t N (τ / 8) := by rw [Rloc]; positivity
  have hmain := hloc p.L p.hL k hk a' q (fun x => ‖innerId p.L (mSig p.E) p.t σ' a' q x‖)
    ((N : ℝ) ^ (τ / 4)) ((N : ℝ) ^ (τ / 4)) (Xt p.L p.E p.t) (etaT p.E p.t) (ellT p.L p.t) ε
    (Rloc p.L p.t N (τ / 8)) hNτ4 hNτ4 hX0 hη0 (by linarith) hε.le hR0
    (fun x => hA ⟨p, ⟨(σ', q), hq⟩, a', x⟩) (fun x => hB ⟨p, σ', q, a', x⟩)
  refine hmain.trans ?_
  -- term 1
  have hlogL : Real.log p.L ≤ Real.log N :=
    Real.log_le_log (by have := p.hL; exact_mod_cast (show 0 < p.L by omega)) p.L_le
  have t1 : (N : ℝ) ^ (τ / 4) * Xt p.L p.E p.t ^ (k - 2) *
      (((k : ℝ) - 1) * (5 + 4 * Real.log p.L))
        ≤ Xt p.L p.E p.t ^ (k - 2) * ((N : ℝ) ^ τ / 3) := by
    have hX2 : 0 ≤ Xt p.L p.E p.t ^ (k - 2) := pow_nonneg hX0 _
    calc (N : ℝ) ^ (τ / 4) * Xt p.L p.E p.t ^ (k - 2) *
          (((k : ℝ) - 1) * (5 + 4 * Real.log p.L))
        ≤ (N : ℝ) ^ (τ / 4) * Xt p.L p.E p.t ^ (k - 2) *
          (((k : ℝ) - 1) * (5 + 4 * Real.log N)) := by gcongr
      _ = Xt p.L p.E p.t ^ (k - 2) *
          ((N : ℝ) ^ (τ / 4) * (((k : ℝ) - 1) * (5 + 4 * Real.log N))) := by ring
      _ ≤ Xt p.L p.E p.t ^ (k - 2) * ((N : ℝ) ^ τ / 3) := by gcongr
  -- term 2
  have hball := ball_term_le p.L p.hL hE2 p.ht0 p.ht1 (k := k) (by omega) hN1 hτ8.le
  have t2 : (N : ℝ) ^ (τ / 4) * Xt p.L p.E p.t ^ (k - 1) * etaT p.E p.t *
      (((k : ℝ) - 1) * (2 * Rloc p.L p.t N (τ / 8) + 1) ^ 2)
        ≤ Xt p.L p.E p.t ^ (k - 2) * ((N : ℝ) ^ τ / 3) := by
    have hX2 : 0 ≤ Xt p.L p.E p.t ^ (k - 2) := pow_nonneg hX0 _
    calc (N : ℝ) ^ (τ / 4) * Xt p.L p.E p.t ^ (k - 1) * etaT p.E p.t *
          (((k : ℝ) - 1) * (2 * Rloc p.L p.t N (τ / 8) + 1) ^ 2)
        = (N : ℝ) ^ (τ / 4) * ((k : ℝ) - 1) * (Xt p.L p.E p.t ^ (k - 1) * etaT p.E p.t *
            (2 * Rloc p.L p.t N (τ / 8) + 1) ^ 2) := by ring
      _ ≤ (N : ℝ) ^ (τ / 4) * ((k : ℝ) - 1) *
            (9 * ((N : ℝ) ^ (τ / 8)) ^ 2 * Xt p.L p.E p.t ^ (k - 2)) := by gcongr
      _ = Xt p.L p.E p.t ^ (k - 2) *
            ((N : ℝ) ^ (τ / 4) * (((k : ℝ) - 1) * (9 * ((N : ℝ) ^ (τ / 8)) ^ 2))) := by ring
      _ ≤ Xt p.L p.E p.t ^ (k - 2) * ((N : ℝ) ^ τ / 3) := by gcongr
  -- term 3
  have t3 : (if (p.L : ℝ) ≤ Rloc p.L p.t N (τ / 8) then 0
      else (N : ℝ) ^ (τ / 4) * Xt p.L p.E p.t ^ (k - 1) * ((k : ℝ) - 1) *
        Real.exp (-ε * Rloc p.L p.t N (τ / 8) / ellT p.L p.t) * (p.L : ℝ) ^ 2)
        ≤ Xt p.L p.E p.t ^ (k - 2) * ((N : ℝ) ^ τ / 3) := by
    have hX2 : 0 ≤ Xt p.L p.E p.t ^ (k - 2) := pow_nonneg hX0 _
    have hNτ : 0 ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
    split_ifs with hLR
    · positivity
    · push Not at hLR
      have hℓL : ellT p.L p.t < p.L := by
        have : ellT p.L p.t ≤ Rloc p.L p.t N (τ / 8) := by
          rw [Rloc]; nlinarith
        linarith
      have hXle := Xt_le_of_ellT_lt p.L hκ p.hE p.ht1 hℓL
      have hexp : -ε * Rloc p.L p.t N (τ / 8) / ellT p.L p.t = -ε * (N : ℝ) ^ (τ / 8) := by
        rw [Rloc]; field_simp
      rw [hexp]
      have hpowk : Xt p.L p.E p.t ^ (k - 1) = Xt p.L p.E p.t ^ (k - 2) * Xt p.L p.E p.t := by
        rw [← pow_succ]; congr 1; omega
      rw [hpowk]
      have hL2 := p.L_sq_le
      have hk0 : 0 ≤ (k : ℝ) - 1 := hk1
      calc (N : ℝ) ^ (τ / 4) * (Xt p.L p.E p.t ^ (k - 2) * Xt p.L p.E p.t) * ((k : ℝ) - 1) *
            Real.exp (-ε * (N : ℝ) ^ (τ / 8)) * (p.L : ℝ) ^ 2
          ≤ (N : ℝ) ^ (τ / 4) * (Xt p.L p.E p.t ^ (k - 2) * Xκ) * ((k : ℝ) - 1) *
            Real.exp (-ε * (N : ℝ) ^ (τ / 8)) * (N : ℝ) := by gcongr
        _ = Xt p.L p.E p.t ^ (k - 2) * ((N : ℝ) ^ (τ / 4) * Xκ * ((k : ℝ) - 1) *
            Real.exp (-ε * (N : ℝ) ^ (τ / 8)) * N) := by ring
        _ ≤ Xt p.L p.E p.t ^ (k - 2) * ((N : ℝ) ^ τ / 3) := by gcongr
  have := add_le_add (add_le_add t1 t2) t3
  linarith

/-- **The inner sums from the lattice counts**: `spwow3At`, the crude bound and the two lattice
counts give the inner-sum bound. -/
private theorem innerSum_of_pins (h3 : spwow3At_pin) (hcr : innerCrude_pin)
    (hball : card_ball_pin) (hlog : sum_inv_sq_pin) : innerSum_pin :=
  S10b_holds h3 hcr (localize_of_counts hball hlog)

end Sum

/-- **The inner sum** (the induction input of `ML:Kbound+pi`): for `k ≥ 3` and a
long root leaf `σ'_p ≠ σ'_{p+1}`,
`Σ_{u ∈ Z_L²} |A(u)| ≺ X_t^{k-2}`, `X_t = (ℓ_t² η_t)⁻¹`.  Conditional on `Prop5Hyp κ c` and
`Prop6Hyp κ`.  Proof: `innerSum_of_pins` (via `S10b_holds`) with
`Kpi_empty_spwow3At_prec`, `innerId_crude_prec`, `card_ball_le`, `sum_inv_sq_le`. -/
theorem innerId_sum_prec :
  ∀ (k : ℕ) [NeZero k], 3 ≤ k → ∀ κ c : ℝ, 0 < κ → 0 < c → Prop5Hyp κ c → Prop6Hyp κ →
    UnifDetDom
      (U := fun N => (p : Par κ N) × {q : (Fin k → Bool) × Fin k // q.1 q.2 ≠ q.1 (q.2 + 1)} ×
        (Fin k → Z2 p.L))
      (fun _ u => ∑ x : Z2 u.1.L,
        ‖innerId u.1.L (mSig u.1.E) u.1.t u.2.1.1.1 u.2.2 u.2.1.1.2 x‖)
      (fun _ u => Xt u.1.L u.1.E u.1.t ^ (k - 2)) :=
  innerSum_of_pins Kpi_empty_spwow3At_prec innerId_crude_prec card_ball_le sum_inv_sq_le

end RBM.KLoop
