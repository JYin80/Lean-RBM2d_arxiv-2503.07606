/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.SumZeroQ
import RBM2D.Propagator.Prop5
import RBM2D.Propagator.Harmonic
import RBM2D.Loop.LatticeCount
import RBM2D.Path.ScalesBridge

/-!
# The bounds on `𝒬_t`

The theorems `qopNorm : QopNorm` and `qopDecay : QopDecay` (the statements of
`RBM2D.Induction.HierVocab`, section 2; `normQA`, `lem_+Q`, decay clause in the corrected form: far
entries of `𝒬_t𝒜` are `≤ W^{-D}(2 + ‖𝒜‖_max)`).

Proof (`d = 2`, `Z2 L`, `N = W²L²`, `N^𝔠 ≤ W`):
* `|(𝒬_t𝒜)_a| ≤ |𝒜_a| + |(𝒫𝒜)_{a₁}| |ϑ_{t,a}|`;
* `|(𝒫𝒜)_{a₁}| ≤ (2R+1)^{2(k-1)}‖𝒜‖_max + L^{2(k-1)}W^{-D}` with `R = ℓ_tW^τ`
  (window count `card_ball_le`, far part from `HasDecay`);
* `|ϑ_{t,a}| ≤ (C₅(1+log L)ℓ_t^{-2})^{k-1}` from property 5 at `ξ = t` (`κ(t)² = 1-t`,
  `ℓ̂(t) = ℓ_t`, `C₅ = 180·40002²`), with the factor `exp(-|a₁-a_i|_L/(20000ℓ_t))` per slot;
* if `maxDist a ≥ R` some slot is `≥ R/2` away from `a₁`, which gives `exp(-W^τ/40000)`.

The `(1+log L)` loss of property 5 is absorbed by `W^{cPrec 𝔠 k · τ}` through `1 + log N ≤ N^ε`
(`one_add_log_detDom_one`); the far factor `exp(-W^τ/40000)` beats every power of `W` via
`x^m/m! ≤ exp x`.

The argument parallels the one-dimensional formalization, with the `d = 1` kernel bound (2.52)
replaced by property 5 of `Θ` on `Z2 L` (`norm_Theta_apply_le_prop5`): the window-sum bound
`QopBounds_norm_Psum_le`, the far slot `QopBounds_exists_far`, the bounds on `ϑ`
`QopBounds_norm_vartheta_le`, `QopBounds_norm_vartheta_le_far`, and the far bound
`QopBounds_pointwise_far`.  The bound on `ϑ̇` is not needed: `QopNorm` and `QopDecay` do not involve
it.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Finset Matrix RBM RBM.Path RBM.Evol

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-! ## 1. The bound on `ϑ_t` from property 5 -/

/-- The constant `C₅ = 180·40002²` of `norm_Theta_apply_le_prop5`. -/
private def QopBounds_C5 : ℝ := 180 * 40002 ^ 2

private theorem QopBounds_C5_pos : 0 < QopBounds_C5 := by unfold QopBounds_C5; positivity

private theorem QopBounds_one_le_C5 : 1 ≤ QopBounds_C5 := by unfold QopBounds_C5; norm_num

/-- `‖1 - t‖ = 1 - t` for `t ≤ 1`. -/
private theorem QopBounds_norm_one_sub {t : ℝ} (ht : t ≤ 1) : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := by
  have h : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_real, Real.norm_of_nonneg (by linarith)]

/-- Property 5 at `ξ = t ∈ [0,1)` (`κ(t)² = 1 - t`, `ℓ̂(t) = ℓ_t`):
`(1-t)|Θ_t(x,y)| ≤ C₅(1+log L)ℓ_t^{-2}exp(-|x-y|_L/(20000ℓ_t))`. -/
private theorem QopBounds_norm_Theta (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (x y : Z2 L) :
    (1 - t) * ‖Theta L (t : ℂ) x y‖ ≤ QopBounds_C5 * (1 + Real.log L) * (ellT L t ^ 2)⁻¹ *
      Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L t)) := by
  have hξ : ‖(t : ℂ)‖ < 1 := by
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have h5 := norm_Theta_apply_le_prop5 L hL (t : ℂ) hξ x y
  have hell : ellhat L (t : ℂ) = ellT L t := kloop_ellT_eq ht1.le
  have hkap : kappa (t : ℂ) ^ 2 = 1 - t := by
    rw [kappa_sq, QopBounds_norm_one_sub ht1.le]
  rw [hell, hkap] at h5
  have h1t : 0 < 1 - t := by linarith
  have hlog : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  calc (1 - t) * ‖Theta L (t : ℂ) x y‖
      ≤ (1 - t) * (180 * 40002 ^ 2 * (1 + Real.log L) * ((1 - t) * ellT L t ^ 2)⁻¹ *
          Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L t))) :=
        mul_le_mul_of_nonneg_left h5 h1t.le
    _ = QopBounds_C5 * (1 + Real.log L) * (ellT L t ^ 2)⁻¹ *
          Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L t)) := by
        unfold QopBounds_C5
        rw [mul_inv]
        field_simp

/-- `‖ϑ_{t,a}‖ = Π_{i ≠ 0} (1-t)‖Θ_t(a₀,a_i)‖`. -/
private theorem QopBounds_norm_vartheta_eq {t : ℝ} (ht1 : t < 1) (a : Fin k → Z2 L) :
    ‖vartheta L t a‖ = ∏ i ∈ Finset.univ.erase (0 : Fin k),
      ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖) := by
  unfold vartheta
  rw [norm_mul, norm_pow, norm_prod, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]

/-- The slot bound `c_L(t) = C₅(1+log L)ℓ_t^{-2}`. -/
private def QopBounds_c (L : ℕ) (t : ℝ) : ℝ :=
  QopBounds_C5 * (1 + Real.log L) * (ellT L t ^ 2)⁻¹

private theorem QopBounds_c_nonneg : 0 ≤ QopBounds_c L t := by
  have hlog : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  unfold QopBounds_c
  exact mul_nonneg (mul_nonneg QopBounds_C5_pos.le hlog) (inv_nonneg.mpr (sq_nonneg _))

/-- `|ϑ_{t,a}| ≤ c^{k-1}`. -/
private theorem QopBounds_norm_vartheta_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : Fin k → Z2 L) : ‖vartheta L t a‖ ≤ QopBounds_c L t ^ (k - 1) := by
  rw [QopBounds_norm_vartheta_eq ht1]
  calc ∏ i ∈ Finset.univ.erase (0 : Fin k), ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖)
      ≤ ∏ _i ∈ Finset.univ.erase (0 : Fin k), QopBounds_c L t := by
        refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
        · exact mul_nonneg (by linarith) (norm_nonneg _)
        · refine (QopBounds_norm_Theta hL ht0 ht1 _ _).trans ?_
          unfold QopBounds_c
          refine mul_le_of_le_one_right ?_ (Real.exp_le_one_iff.mpr ?_)
          · have hlog : 0 ≤ 1 + Real.log L := by
              have := Real.log_natCast_nonneg L
              linarith
            exact mul_nonneg (mul_nonneg QopBounds_C5_pos.le hlog) (inv_nonneg.mpr (sq_nonneg _))
          · have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht1).1
            exact div_nonpos_of_nonpos_of_nonneg (by simp) (by positivity)
    _ = QopBounds_c L t ^ (k - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]

/-- `|ϑ_{t,a}| ≤ c^{k-1} exp(-r/(20000ℓ_t))` if slot `m ≠ 0` is `≥ r` away from `a₀`. -/
private theorem QopBounds_norm_vartheta_le_far (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : Fin k → Z2 L) {r : ℝ} {m : Fin k} (hm : m ∈ Finset.univ.erase (0 : Fin k))
    (hr : r ≤ (zdist2 L (a 0 - a m) : ℝ)) :
    ‖vartheta L t a‖ ≤ QopBounds_c L t ^ (k - 1) * Real.exp (-r / (20000 * ellT L t)) := by
  have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht1).1
  have hc0 : 0 ≤ QopBounds_c L t := QopBounds_c_nonneg
  rw [QopBounds_norm_vartheta_eq ht1]
  set e := Real.exp (-r / (20000 * ellT L t)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hfac : ∀ i ∈ Finset.univ.erase (0 : Fin k),
      (1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖ ≤ QopBounds_c L t * (if i = m then e else 1) := by
    intro i hi
    have h1 := QopBounds_norm_Theta hL ht0 ht1 (a 0) (a i)
    have hpre : 0 ≤ QopBounds_C5 * (1 + Real.log L) * (ellT L t ^ 2)⁻¹ := hc0
    split_ifs with him
    · subst him
      refine h1.trans ?_
      unfold QopBounds_c
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hpre
      exact div_le_div_of_nonneg_right (neg_le_neg hr) (by positivity)
    · rw [mul_one]
      refine h1.trans ?_
      unfold QopBounds_c
      refine mul_le_of_le_one_right hpre (Real.exp_le_one_iff.mpr ?_)
      exact div_nonpos_of_nonpos_of_nonneg (by simp) (by positivity)
  have hme : (if m ∈ Finset.univ.erase (0 : Fin k) then e else 1) = e := by
    simp only [hm, ↓reduceIte]
  calc ∏ i ∈ Finset.univ.erase (0 : Fin k), ((1 - t) * ‖Theta L (t : ℂ) (a 0) (a i)‖)
      ≤ ∏ i ∈ Finset.univ.erase (0 : Fin k), (QopBounds_c L t * (if i = m then e else 1)) :=
        Finset.prod_le_prod₀ (fun i _ => mul_nonneg (by linarith) (norm_nonneg _)) hfac
    _ = QopBounds_c L t ^ (k - 1) * e := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' (Finset.univ.erase (0 : Fin k)) m
          (fun _ => e), hme, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin]

/-! ## 2. The slot sums `𝒫𝒜` and the far index -/

/-- `‖A a‖ ≤ ‖A‖_max`. -/
private theorem QopBounds_le_tmax (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    ‖A a‖ ≤ tmax L A :=
  Finset.le_sup' (fun a => ‖A a‖) (Finset.mem_univ a)

private theorem QopBounds_tmax_nonneg (A : (Fin k → Z2 L) → ℂ) : 0 ≤ tmax L A :=
  (norm_nonneg _).trans (QopBounds_le_tmax A 0)

private theorem QopBounds_tmax_le {A : (Fin k → Z2 L) → ℂ} {B : ℝ} (h : ∀ a, ‖A a‖ ≤ B) :
    tmax L A ≤ B :=
  Finset.sup'_le _ _ fun a _ => h a

/-- `|-x|_L = |x|_L` on `Z_L`. -/
private theorem QopBounds_zdist_neg (x : ZMod L) : zdist L (-x) = zdist L x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hlt := ZMod.val_lt x
    have hv : (-x).val = L - x.val := by
      simp [ZMod.neg_val, hx]
    simp only [zdist, hv]
    omega

private theorem QopBounds_zdist2_neg (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, QopBounds_zdist_neg]

/-- A pair of slots at distance `≥ R` forces a slot `m ≠ 0` at distance `≥ R/2` from `a₀`. -/
private theorem QopBounds_exists_far {R : ℝ} (hR : 0 < R) {a : Fin k → Z2 L}
    (h : R ≤ (KLoop.maxDist L a : ℝ)) :
    ∃ m ∈ Finset.univ.erase (0 : Fin k), R / 2 ≤ (zdist2 L (a 0 - a m) : ℝ) := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k × Fin k))
    Finset.univ_nonempty (fun p : Fin k × Fin k => zdist2 L (a p.1 - a p.2))
  have hmax : KLoop.maxDist L a = zdist2 L (a p.1 - a p.2) := hp
  have hij : R ≤ (zdist2 L (a p.1 - a p.2) : ℝ) := by
    rw [← hmax]; exact h
  have htri : zdist2 L (a p.1 - a p.2) ≤ zdist2 L (a 0 - a p.1) + zdist2 L (a 0 - a p.2) := by
    have h1 := zdist2_add_le L (a 0 - a p.2) (-(a 0 - a p.1))
    have e : a 0 - a p.2 + -(a 0 - a p.1) = a p.1 - a p.2 := by abel
    rw [e, QopBounds_zdist2_neg] at h1
    omega
  have htri' : (zdist2 L (a p.1 - a p.2) : ℝ) ≤
      (zdist2 L (a 0 - a p.1) : ℝ) + (zdist2 L (a 0 - a p.2) : ℝ) := by exact_mod_cast htri
  have key : ∀ m : Fin k, R / 2 ≤ (zdist2 L (a 0 - a m) : ℝ) →
      ∃ m ∈ Finset.univ.erase (0 : Fin k), R / 2 ≤ (zdist2 L (a 0 - a m) : ℝ) := by
    intro m hm
    refine ⟨m, ?_, hm⟩
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    simp at hm
    linarith
  by_cases h1 : R / 2 ≤ (zdist2 L (a 0 - a p.1) : ℝ)
  · exact key _ h1
  · apply key p.2
    push Not at h1
    linarith

/-- The window-sum bound `|𝒫𝒜| ≤ ((2R+1)²)^{k-1}M + (L²)^{k-1}δ` for a tensor bounded by `M` with
`|𝒜_a| ≤ δ` whenever `maxDist a ≥ R` (the window count is
`RBM.KLoop.card_ball_le`, `(2R+1)²` points of `Z_L²` per slot). -/
private theorem QopBounds_norm_Psum_le {R M δ : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (A : (Fin k → Z2 L) → ℂ) (hAM : ∀ b, ‖A b‖ ≤ M)
    (hAδ : ∀ b, R ≤ (KLoop.maxDist L b : ℝ) → ‖A b‖ ≤ δ) (a₁ : Z2 L) :
    ‖Psum L A a₁‖ ≤ ((2 * R + 1) ^ 2) ^ (k - 1) * M + ((L : ℝ) ^ 2) ^ (k - 1) * δ := by
  classical
  set F : Finset (Fin k → Z2 L) := Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁) with hF
  set ball : Z2 L → ℝ := fun b => if (zdist2 L (a₁ - b) : ℝ) ≤ R then 1 else 0 with hball
  have hball0 : ∀ b, 0 ≤ ball b := fun b => by
    simp only [hball]
    split_ifs <;> norm_num
  have hpt : ∀ a ∈ F, ‖A a‖ ≤ M * ∏ i ∈ Finset.univ.erase (0 : Fin k), ball (a i) + δ := by
    intro a ha
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    by_cases hall : ∀ i ∈ Finset.univ.erase (0 : Fin k), (zdist2 L (a₁ - a i) : ℝ) ≤ R
    · have h1 : ∏ i ∈ Finset.univ.erase (0 : Fin k), ball (a i) = 1 :=
        Finset.prod_eq_one fun i hi => by simp [hball, hall i hi]
      rw [h1, mul_one]
      linarith [hAM a]
    · push Not at hall
      obtain ⟨i, hi, hlt⟩ := hall
      have hmax : R ≤ (KLoop.maxDist L a : ℝ) := by
        have hle : zdist2 L (a 0 - a i) ≤ KLoop.maxDist L a :=
          Finset.le_sup (f := fun p : Fin k × Fin k => zdist2 L (a p.1 - a p.2))
            (Finset.mem_univ (0, i))
        have h2 : (zdist2 L (a 0 - a i) : ℝ) ≤ (KLoop.maxDist L a : ℝ) := by exact_mod_cast hle
        rw [ha0] at h2
        linarith
      have h1 := hAδ a hmax
      have h2 : 0 ≤ M * ∏ i ∈ Finset.univ.erase (0 : Fin k), ball (a i) :=
        mul_nonneg hM (Finset.prod_nonneg fun j _ => hball0 _)
      linarith
  have hsum : ∑ a ∈ F, ∏ i ∈ Finset.univ.erase (0 : Fin k), ball (a i)
      = ∏ i ∈ Finset.univ.erase (0 : Fin k), ∑ b : Z2 L, ball b :=
    SumZeroQ_sum_filter_prod a₁ (fun _ b => ball b)
  have hcard : ∑ b : Z2 L, ball b ≤ (2 * R + 1) ^ 2 := by
    have := KLoop.card_ball_le L a₁ R hR
    simp only [hball, Finset.sum_boole]
    exact this
  have hprod : ∏ i ∈ Finset.univ.erase (0 : Fin k), ∑ b : Z2 L, ball b
      ≤ ((2 * R + 1) ^ 2) ^ (k - 1) := by
    calc ∏ i ∈ Finset.univ.erase (0 : Fin k), ∑ b : Z2 L, ball b
        ≤ ∏ _i ∈ Finset.univ.erase (0 : Fin k), (2 * R + 1) ^ 2 :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun b _ => hball0 b)
            (fun i _ => hcard)
      _ = ((2 * R + 1) ^ 2) ^ (k - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin]
  unfold Psum
  calc ‖∑ a ∈ F, A a‖ ≤ ∑ a ∈ F, ‖A a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ F, (M * ∏ i ∈ Finset.univ.erase (0 : Fin k), ball (a i) + δ) :=
        Finset.sum_le_sum hpt
    _ = M * ∑ a ∈ F, ∏ i ∈ Finset.univ.erase (0 : Fin k), ball (a i) + (F.card : ℝ) * δ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ M * ((2 * R + 1) ^ 2) ^ (k - 1) + ((L : ℝ) ^ 2) ^ (k - 1) * δ := by
        rw [hsum, hF, SumZeroQ_card_filter]
        gcongr
    _ = ((2 * R + 1) ^ 2) ^ (k - 1) * M + ((L : ℝ) ^ 2) ^ (k - 1) * δ := by ring

/-- The crude bound `|𝒫𝒜| ≤ (L²)^{k-1}M`. -/
private theorem QopBounds_norm_Psum_le_crude {M : ℝ} (A : (Fin k → Z2 L) → ℂ)
    (hAM : ∀ b, ‖A b‖ ≤ M) (a₁ : Z2 L) :
    ‖Psum L A a₁‖ ≤ ((L : ℝ) ^ 2) ^ (k - 1) * M := by
  unfold Psum
  calc ‖∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁), A a‖
      ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁), ‖A a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin k → Z2 L => a 0 = a₁), M :=
        Finset.sum_le_sum fun a _ => hAM a
    _ = ((L : ℝ) ^ 2) ^ (k - 1) * M := by
        rw [Finset.sum_const, nsmul_eq_mul, SumZeroQ_card_filter]

/-! ## 3. The pointwise estimates on `𝒬_t𝒜` -/

/-- `|(𝒬_t𝒜)_a| ≤ ‖𝒜‖ + ((2R+1)^{2(k-1)}‖𝒜‖ + L^{2(k-1)}W^{-D}) c^{k-1}`, `R = ℓ_tW^τ`. -/
private theorem QopBounds_pointwise (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {W : ℕ} [NeZero W] {τ D : ℝ} {A : (Fin k → Z2 L) → ℂ} (hA : HasDecay L W t τ D A)
    (a : Fin k → Z2 L) :
    ‖Qop L t A a‖ ≤ tmax L A +
      (((2 * (ellT L t * (W : ℝ) ^ τ) + 1) ^ 2) ^ (k - 1) * tmax L A +
        ((L : ℝ) ^ 2) ^ (k - 1) * (W : ℝ) ^ (-D)) * QopBounds_c L t ^ (k - 1) := by
  have h1 : ‖Qop L t A a‖ ≤ ‖A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ := by
    unfold Qop
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
  have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht1).1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hR : 0 ≤ ellT L t * (W : ℝ) ^ τ := by positivity
  have hP := QopBounds_norm_Psum_le hR (QopBounds_tmax_nonneg A)
    (Real.rpow_nonneg hW0.le _) A (QopBounds_le_tmax A) hA (a 0)
  have hϑ := QopBounds_norm_vartheta_le hL ht0 ht1 a
  have hc0 : 0 ≤ QopBounds_c L t ^ (k - 1) := pow_nonneg QopBounds_c_nonneg _
  have hPnn : 0 ≤ ((2 * (ellT L t * (W : ℝ) ^ τ) + 1) ^ 2) ^ (k - 1) * tmax L A +
        ((L : ℝ) ^ 2) ^ (k - 1) * (W : ℝ) ^ (-D) :=
    add_nonneg (mul_nonneg (by positivity) (QopBounds_tmax_nonneg A))
      (mul_nonneg (by positivity) (Real.rpow_nonneg hW0.le _))
  calc ‖Qop L t A a‖ ≤ ‖A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ := h1
    _ ≤ tmax L A + (((2 * (ellT L t * (W : ℝ) ^ τ) + 1) ^ 2) ^ (k - 1) * tmax L A +
        ((L : ℝ) ^ 2) ^ (k - 1) * (W : ℝ) ^ (-D)) * QopBounds_c L t ^ (k - 1) :=
        add_le_add (QopBounds_le_tmax A a) (mul_le_mul hP hϑ (norm_nonneg _) hPnn)

/-- Far entries: `|(𝒬_t𝒜)_a| ≤ W^{-D} + (L²)^{k-1}‖𝒜‖ c^{k-1} exp(-W^τ/40000)` when
`maxDist a ≥ ℓ_tW^τ` (`R/2 = ℓ_tW^τ/2` gives `exp(-R/(2·20000ℓ_t)) = exp(-W^τ/40000)`). -/
private theorem QopBounds_pointwise_far (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {W : ℕ} [NeZero W] {τ D : ℝ} {A : (Fin k → Z2 L) → ℂ} (hA : HasDecay L W t τ D A)
    (a : Fin k → Z2 L) (hfar : ellT L t * (W : ℝ) ^ τ ≤ (KLoop.maxDist L a : ℝ)) :
    ‖Qop L t A a‖ ≤ (W : ℝ) ^ (-D) + ((L : ℝ) ^ 2) ^ (k - 1) * tmax L A *
      (QopBounds_c L t ^ (k - 1) * Real.exp (-((W : ℝ) ^ τ) / 40000)) := by
  have h1 : ‖Qop L t A a‖ ≤ ‖A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ := by
    unfold Qop
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
  have hℓ : 0 < ellT L t := (ellT_pos_le (by omega) ht1).1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hR : 0 < ellT L t * (W : ℝ) ^ τ := by positivity
  obtain ⟨m, hm, hmr⟩ := QopBounds_exists_far hR hfar
  have hϑ := QopBounds_norm_vartheta_le_far hL ht0 ht1 a hm hmr
  have hexp : -(ellT L t * (W : ℝ) ^ τ / 2) / (20000 * ellT L t) = -((W : ℝ) ^ τ) / 40000 := by
    field_simp
    ring
  rw [hexp] at hϑ
  have hP := QopBounds_norm_Psum_le_crude A (QopBounds_le_tmax A) (a 0)
  have hA1 : ‖A a‖ ≤ (W : ℝ) ^ (-D) := hA a hfar
  have hPnn : 0 ≤ ((L : ℝ) ^ 2) ^ (k - 1) * tmax L A :=
    mul_nonneg (by positivity) (QopBounds_tmax_nonneg A)
  calc ‖Qop L t A a‖ ≤ ‖A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ := h1
    _ ≤ (W : ℝ) ^ (-D) + ((L : ℝ) ^ 2) ^ (k - 1) * tmax L A *
        (QopBounds_c L t ^ (k - 1) * Real.exp (-((W : ℝ) ^ τ) / 40000)) :=
        add_le_add hA1 (mul_le_mul hP hϑ (norm_nonneg _) hPnn)

/-! ## 4. The numerical core (exponents of `W`) -/

/-- `(x^s)^m = x^(s m)` for `x ≥ 0`. -/
private theorem QopBounds_rpow_pow {x : ℝ} (hx : 0 ≤ x) (s : ℝ) (m : ℕ) :
    (x ^ s) ^ m = x ^ (s * m) :=
  (Real.rpow_mul_natCast hx s m).symm

/-- A statement that holds eventually in `x ∈ ℝ` holds for every `x ≥ N^𝔠`, eventually in `N`
(`W ≥ N^𝔠 → ∞`). -/
private theorem QopBounds_eventually_of_atTop {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {P : ℝ → Prop}
    (hP : ∀ᶠ x : ℝ in Filter.atTop, P x) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ x : ℝ, (N : ℝ) ^ 𝔠 ≤ x → P x := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hP
  have h := ((tendsto_rpow_atTop h𝔠).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop x₀
  filter_upwards [h] with N hN x hx
  exact hx₀ x (hN.trans hx)

/-- `N^𝔠 ≤ W` gives `N ≤ W^{1/𝔠}`. -/
private theorem QopBounds_N_le {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {N : ℕ} {Wr : ℝ}
    (h : (N : ℝ) ^ 𝔠 ≤ Wr) : (N : ℝ) ≤ Wr ^ 𝔠⁻¹ := by
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) = ((N : ℝ) ^ 𝔠) ^ 𝔠⁻¹ := by
        rw [← Real.rpow_mul h0, mul_inv_cancel₀ h𝔠.ne', Real.rpow_one]
    _ ≤ Wr ^ 𝔠⁻¹ := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) h (inv_nonneg.mpr h𝔠.le)

/-- **Numerical core of `qopNorm`, the factor of `‖𝒜‖_max`**: with `Lam = 9C₅(1+log L)`, the
`(1 + log L)` loss is absorbed by `W^{b/2}` and
`1 + (Lam W^{2τ})^{k-1} ≤ W^{b + 2τ(k-1)} = W^{cPrec 𝔠 k · τ}`. -/
private theorem QopBounds_num_factor {Wr Lam τ b cPt : ℝ} {m : ℕ} (hWr : 1 ≤ Wr)
    (hLam : 1 ≤ Lam) (hτ : 0 < τ)
    (hLam9 : Lam ^ m ≤ (9 * QopBounds_C5) ^ m * Wr ^ (b / 2))
    (hW3 : 2 * (9 * QopBounds_C5) ^ m ≤ Wr ^ (b / 2)) (hcP : cPt = b + 2 * τ * m) :
    1 + (Lam * (Wr ^ τ) ^ 2) ^ m ≤ Wr ^ cPt := by
  have hW0 : 0 < Wr := by linarith
  have h1 : ((Wr ^ τ) ^ 2) ^ m = Wr ^ (2 * τ * m) := by
    rw [← pow_mul, ← Real.rpow_mul_natCast hW0.le τ (2 * m)]
    congr 1
    push_cast
    ring
  have hL1 : 1 ≤ Lam ^ m := one_le_pow₀ hLam
  have hW1 : 1 ≤ Wr ^ (2 * τ * m) := Real.one_le_rpow hWr (by positivity)
  rw [mul_pow, h1]
  have hX : 1 ≤ Lam ^ m * Wr ^ (2 * τ * m) := one_le_mul_of_one_le_of_one_le hL1 hW1
  have hpos : 0 ≤ Wr ^ (2 * τ * m) := hW1.trans' zero_le_one
  calc 1 + Lam ^ m * Wr ^ (2 * τ * m) ≤ 2 * (Lam ^ m * Wr ^ (2 * τ * m)) := by linarith
    _ ≤ 2 * (((9 * QopBounds_C5) ^ m * Wr ^ (b / 2)) * Wr ^ (2 * τ * m)) := by gcongr
    _ = (2 * (9 * QopBounds_C5) ^ m) * Wr ^ (b / 2) * Wr ^ (2 * τ * m) := by ring
    _ ≤ Wr ^ (b / 2) * Wr ^ (b / 2) * Wr ^ (2 * τ * m) := by
        gcongr
    _ = Wr ^ cPt := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, hcP]
        congr 1
        ring

/-- **Numerical core, the additive term**: `L² ≤ W^pp` and `c ≤ W · W^pp` give
`(L²c)^m ≤ W^{(1+2pp)m} ≤ W^cPt`. -/
private theorem QopBounds_num_add {Wr L2 c pp cPt : ℝ} {m : ℕ} (hWr : 1 ≤ Wr)
    (hL2 : L2 ≤ Wr ^ pp) (hL20 : 0 ≤ L2) (hc : c ≤ Wr * Wr ^ pp) (hc0 : 0 ≤ c)
    (hcP : (1 + 2 * pp) * m ≤ cPt) : (L2 * c) ^ m ≤ Wr ^ cPt := by
  have hW0 : 0 < Wr := by linarith
  have h1 : L2 * c ≤ Wr ^ (1 + 2 * pp) := by
    calc L2 * c ≤ Wr ^ pp * (Wr * Wr ^ pp) := mul_le_mul hL2 hc hc0 (Real.rpow_nonneg hW0.le _)
      _ = Wr ^ (1 + 2 * pp) := by
          rw [show (1 + 2 * pp) = 1 + pp + pp by ring, Real.rpow_add hW0, Real.rpow_add hW0,
            Real.rpow_one]
          ring
  calc (L2 * c) ^ m ≤ (Wr ^ (1 + 2 * pp)) ^ m := pow_le_pow_left₀ (mul_nonneg hL20 hc0) h1 m
    _ = Wr ^ ((1 + 2 * pp) * m) := QopBounds_rpow_pow hW0.le _ _
    _ ≤ Wr ^ cPt := Real.rpow_le_rpow_of_exponent_le hWr hcP

/-- **`x^q ≤ exp(x^τ/40000)` eventually**: `x^n/n! ≤ exp x` with `nτ ≥ q + 1` and `x ≥ 40000^n n!`. -/
private theorem QopBounds_rpow_le_exp {τ : ℝ} (hτ : 0 < τ) (q : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, x ^ q ≤ Real.exp (x ^ τ / 40000) := by
  set n : ℕ := ⌈(q + 1) / τ⌉₊ with hn
  have hnτ : q + 1 ≤ τ * n := by
    have h := Nat.le_ceil ((q + 1) / τ)
    rw [div_le_iff₀ hτ] at h
    linarith
  filter_upwards [Filter.eventually_ge_atTop (40000 ^ n * (n.factorial : ℝ)),
    Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hK : 0 < (40000 : ℝ) ^ n * (n.factorial : ℝ) := by positivity
  have h1 : (x ^ τ / 40000) ^ n / n.factorial ≤ Real.exp (x ^ τ / 40000) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have h2 : (x ^ τ / 40000) ^ n / n.factorial = x ^ (τ * n) / (40000 ^ n * n.factorial) := by
    rw [div_pow, Real.rpow_mul_natCast hx0.le]
    field_simp
  have h3 : x ^ q * (40000 ^ n * n.factorial) ≤ x ^ (τ * n) := by
    calc x ^ q * (40000 ^ n * n.factorial) ≤ x ^ q * x :=
          mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hx0.le _)
      _ = x ^ (q + 1) := by rw [Real.rpow_add hx0, Real.rpow_one]
      _ ≤ x ^ (τ * n) := Real.rpow_le_rpow_of_exponent_le hx1 hnτ
  calc x ^ q = x ^ q * (40000 ^ n * n.factorial) / (40000 ^ n * n.factorial) := by
        field_simp
    _ ≤ x ^ (τ * n) / (40000 ^ n * n.factorial) := by gcongr
    _ = (x ^ τ / 40000) ^ n / n.factorial := h2.symm
    _ ≤ Real.exp (x ^ τ / 40000) := h1

/-! ## 5. The theorems `qopNorm` and `qopDecay` -/

/-- The window inequality `(2R+1)²c ≤ 9C₅(1+log L)W^{2τ}` (`R = ℓ_tW^τ ≥ 1`, the `ℓ_t²` cancels). -/
private theorem QopBounds_near (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {Wr τ : ℝ}
    (hWr : 1 ≤ Wr) (hτ : 0 < τ) :
    (2 * (ellT L t * Wr ^ τ) + 1) ^ 2 * QopBounds_c L t ≤
      9 * QopBounds_C5 * (1 + Real.log L) * (Wr ^ τ) ^ 2 := by
  have hℓ1 : 1 ≤ ellT L t := one_le_ellT (by omega) ht0 ht1
  have hℓ : 0 < ellT L t := by linarith
  have hy1 : 1 ≤ Wr ^ τ := Real.one_le_rpow hWr hτ.le
  have hR1 : 1 ≤ ellT L t * Wr ^ τ := one_le_mul_of_one_le_of_one_le hℓ1 hy1
  have h1 : (2 * (ellT L t * Wr ^ τ) + 1) ^ 2 ≤ 9 * (ellT L t * Wr ^ τ) ^ 2 := by nlinarith
  calc (2 * (ellT L t * Wr ^ τ) + 1) ^ 2 * QopBounds_c L t
      ≤ 9 * (ellT L t * Wr ^ τ) ^ 2 * QopBounds_c L t :=
        mul_le_mul_of_nonneg_right h1 QopBounds_c_nonneg
    _ = 9 * QopBounds_C5 * (1 + Real.log L) * (Wr ^ τ) ^ 2 := by
        unfold QopBounds_c
        field_simp

/-- `c ≤ C₅(1 + log L) ≤ C₅ L`. -/
private theorem QopBounds_c_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    QopBounds_c L t ≤ QopBounds_C5 * L := by
  have hℓ1 : 1 ≤ ellT L t := one_le_ellT (by omega) ht0 ht1
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hlog : 1 + Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L)
    linarith
  have hinv : (ellT L t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hℓ1)
  have hlog0 : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  unfold QopBounds_c
  calc QopBounds_C5 * (1 + Real.log L) * (ellT L t ^ 2)⁻¹
      ≤ QopBounds_C5 * (1 + Real.log L) * 1 :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg QopBounds_C5_pos.le hlog0)
    _ ≤ QopBounds_C5 * L := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hlog QopBounds_C5_pos.le

/-- The size relations from `W²L² = N` and `N^𝔠 ≤ W`:
`N ≤ W^{1/𝔠}`, `L ≤ N`, `L² ≤ N`, hence `L, L² ≤ W^{1/𝔠}`. -/
private theorem QopBounds_sizes {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {L W N : ℕ} [NeZero W] (hL : 3 ≤ L)
    (hNLW : W ^ 2 * L ^ 2 = N) (hNc : (N : ℝ) ^ 𝔠 ≤ W) :
    (N : ℝ) ≤ (W : ℝ) ^ 𝔠⁻¹ ∧ (L : ℝ) ≤ N ∧ (L : ℝ) ≤ (W : ℝ) ^ 𝔠⁻¹ ∧
      (L : ℝ) ^ 2 ≤ (W : ℝ) ^ 𝔠⁻¹ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hNW' : (N : ℝ) ≤ (W : ℝ) ^ 𝔠⁻¹ := QopBounds_N_le h𝔠 hNc
  have hNeq : (N : ℝ) = (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    rw [← hNLW]
    push_cast
    ring
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL2N : (L : ℝ) ^ 2 ≤ N := by
    rw [hNeq]
    nlinarith [sq_nonneg (L : ℝ), sq_nonneg ((W : ℝ) - 1)]
  have hLN : (L : ℝ) ≤ N := (le_self_pow₀ hL1 two_ne_zero).trans hL2N
  exact ⟨hNW', hLN, hLN.trans hNW', hL2N.trans hNW'⟩

/-- `c ≤ W · W^{pp}` from `C₅ ≤ W` and `L ≤ W^{pp}`. -/
private theorem QopBounds_c_le_W (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {Wr pp : ℝ}
    (hWr0 : 0 ≤ Wr) (hWrC : QopBounds_C5 ≤ Wr) (hLp : (L : ℝ) ≤ Wr ^ pp) :
    QopBounds_c L t ≤ Wr * Wr ^ pp :=
  calc QopBounds_c L t ≤ QopBounds_C5 * L := QopBounds_c_le hL ht0 ht1
    _ ≤ Wr * Wr ^ pp := mul_le_mul hWrC hLp (Nat.cast_nonneg L) hWr0

/-- **`qopNorm`** (the statement `QopNorm` of `RBM2D.Induction.HierVocab`; `normQA`, `lem_+Q`),
with no added hypothesis. -/
theorem qopNorm : QopNorm := by
  intro 𝔠 h𝔠 k _ hk τ D hτ hD
  have hm1 : 1 ≤ k - 1 := by omega
  set m : ℕ := k - 1 with hm
  have hmk : (m : ℝ) = (k : ℝ) - 1 := by
    rw [hm]
    rw [Nat.cast_sub (by omega)]
    simp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set p : ℝ := 𝔠⁻¹ with hp
  have hp0 : 0 < p := inv_pos.mpr h𝔠
  set b : ℝ := (2 * k + 6 + 4 * k / 𝔠) * τ with hb
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hb0 : 0 < b := by positivity
  set ε : ℝ := b * 𝔠 / (2 * m) with hε
  have hε0 : 0 < ε := by positivity
  have hpε : p * ε * m = b / 2 := by
    rw [hp, hε]
    field_simp
  have hE1 : ∀ᶠ N : ℕ in Filter.atTop, 1 + Real.log N ≤ (N : ℝ) ^ ε := by
    filter_upwards [detDom_iff.mp one_add_log_detDom_one ε hε0] with N hN
    simpa using hN
  have hEW := QopBounds_eventually_of_atTop h𝔠
    ((Filter.eventually_ge_atTop (1 : ℝ)).and
      ((Filter.eventually_ge_atTop QopBounds_C5).and
        ((tendsto_rpow_atTop (half_pos hb0)).eventually_ge_atTop (2 * (9 * QopBounds_C5) ^ m))))
  filter_upwards [hE1, hEW] with N hN1 hNW
  intro L W _ _ hL hNLW hNc t ht0 ht1 A hA
  have hWr0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  obtain ⟨hWr1, hWrC, hWr3⟩ := hNW (W : ℝ) hNc
  obtain ⟨hNW', hLN, hLp, hL2p⟩ := QopBounds_sizes h𝔠 hL hNLW hNc
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hcPrec : cPrec 𝔠 k * τ = b + 2 * τ * m := by
    rw [hmk, hb]
    unfold cPrec
    ring
  -- the factor of `‖𝒜‖_max`
  have hlogL : 1 + Real.log L ≤ 1 + Real.log N := by
    have := Real.log_le_log (by linarith : (0 : ℝ) < L) hLN
    linarith
  have hLam1 : 1 ≤ 9 * QopBounds_C5 * (1 + Real.log L) := by
    have hlog0 : 0 ≤ Real.log L := Real.log_natCast_nonneg L
    have := QopBounds_one_le_C5
    nlinarith
  have hLam9 : (9 * QopBounds_C5 * (1 + Real.log L)) ^ m ≤
      (9 * QopBounds_C5) ^ m * (W : ℝ) ^ (b / 2) := by
    have h1 : 9 * QopBounds_C5 * (1 + Real.log L) ≤ 9 * QopBounds_C5 * (W : ℝ) ^ (p * ε) := by
      have h9 : 0 ≤ 9 * QopBounds_C5 := by have := QopBounds_C5_pos; positivity
      calc 9 * QopBounds_C5 * (1 + Real.log L) ≤ 9 * QopBounds_C5 * (N : ℝ) ^ ε :=
            mul_le_mul_of_nonneg_left (hlogL.trans hN1) h9
        _ ≤ 9 * QopBounds_C5 * ((W : ℝ) ^ p) ^ ε :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg N) hNW' hε0.le) h9
        _ = 9 * QopBounds_C5 * (W : ℝ) ^ (p * ε) := by
            rw [← Real.rpow_mul hWr0.le]
    calc (9 * QopBounds_C5 * (1 + Real.log L)) ^ m
        ≤ (9 * QopBounds_C5 * (W : ℝ) ^ (p * ε)) ^ m :=
          pow_le_pow_left₀ (by linarith) h1 m
      _ = (9 * QopBounds_C5) ^ m * ((W : ℝ) ^ (p * ε)) ^ m := mul_pow _ _ _
      _ = (9 * QopBounds_C5) ^ m * (W : ℝ) ^ (b / 2) := by
          rw [QopBounds_rpow_pow hWr0.le, hpε]
  have hfac : 1 + ((2 * (ellT L t * (W : ℝ) ^ τ) + 1) ^ 2 * QopBounds_c L t) ^ m ≤
      (W : ℝ) ^ (cPrec 𝔠 k * τ) := by
    refine le_trans ?_ (QopBounds_num_factor hWr1 hLam1 hτ hLam9 hWr3 hcPrec)
    refine add_le_add_right (pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) QopBounds_c_nonneg)
      (QopBounds_near hL ht0 ht1 hWr1 hτ) m) 1
  -- the additive term
  have hadd : (((L : ℝ) ^ 2) * QopBounds_c L t) ^ m ≤ (W : ℝ) ^ (cPrec 𝔠 k) := by
    refine QopBounds_num_add hWr1 hL2p (sq_nonneg _) (QopBounds_c_le_W hL ht0 ht1 hWr0.le hWrC hLp)
      QopBounds_c_nonneg ?_
    · unfold cPrec
      rw [hmk]
      have : 0 ≤ 𝔠⁻¹ := inv_nonneg.mpr h𝔠.le
      have h4 : 4 * (k : ℝ) / 𝔠 = 4 * k * 𝔠⁻¹ := by rw [div_eq_mul_inv]
      rw [h4]
      nlinarith
  -- assemble
  have hT0 : 0 ≤ tmax L A := QopBounds_tmax_nonneg A
  have hδ0 : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hWr0.le _
  refine QopBounds_tmax_le fun a => ?_
  refine (QopBounds_pointwise hL ht0 ht1 hA a).trans ?_
  have hsplit : tmax L A +
      (((2 * (ellT L t * (W : ℝ) ^ τ) + 1) ^ 2) ^ (k - 1) * tmax L A +
        ((L : ℝ) ^ 2) ^ (k - 1) * (W : ℝ) ^ (-D)) * QopBounds_c L t ^ (k - 1) =
      (1 + ((2 * (ellT L t * (W : ℝ) ^ τ) + 1) ^ 2 * QopBounds_c L t) ^ m) * tmax L A +
        ((((L : ℝ) ^ 2) * QopBounds_c L t) ^ m) * (W : ℝ) ^ (-D) := by
    rw [mul_pow, mul_pow, ← hm]
    ring
  rw [hsplit]
  calc (1 + ((2 * (ellT L t * (W : ℝ) ^ τ) + 1) ^ 2 * QopBounds_c L t) ^ m) * tmax L A +
        ((((L : ℝ) ^ 2) * QopBounds_c L t) ^ m) * (W : ℝ) ^ (-D)
      ≤ (W : ℝ) ^ (cPrec 𝔠 k * τ) * tmax L A + (W : ℝ) ^ (cPrec 𝔠 k) * (W : ℝ) ^ (-D) :=
        add_le_add (mul_le_mul_of_nonneg_right hfac hT0) (mul_le_mul_of_nonneg_right hadd hδ0)
    _ = (W : ℝ) ^ (cPrec 𝔠 k * τ) * tmax L A + (W : ℝ) ^ (-D + cPrec 𝔠 k) := by
        rw [add_comm (-D) (cPrec 𝔠 k), Real.rpow_add hWr0]

/-- **`qopDecay`** (the statement `QopDecay` of `RBM2D.Induction.HierVocab`; `lem_+Q`, decay clause
in the corrected form), with no added hypothesis. -/
theorem qopDecay : QopDecay := by
  intro 𝔠 h𝔠 k _ hk τ D hτ hD
  have hm1 : 1 ≤ k - 1 := by omega
  set m : ℕ := k - 1 with hm
  set p : ℝ := 𝔠⁻¹ with hp
  have hp0 : 0 < p := inv_pos.mpr h𝔠
  set q : ℝ := (1 + 2 * p) * m + D with hq
  have hEW := QopBounds_eventually_of_atTop h𝔠
    ((Filter.eventually_ge_atTop (1 : ℝ)).and
      ((Filter.eventually_ge_atTop QopBounds_C5).and (QopBounds_rpow_le_exp hτ q)))
  filter_upwards [hEW] with N hNW
  intro L W _ _ hL hNLW hNc t ht0 ht1 A hA a hfar
  have hWr0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  obtain ⟨hWr1, hWrC, hWrE⟩ := hNW (W : ℝ) hNc
  obtain ⟨hNW', hLN, hLp, hL2p⟩ := QopBounds_sizes h𝔠 hL hNLW hNc
  have hadd : (((L : ℝ) ^ 2) * QopBounds_c L t) ^ m ≤ (W : ℝ) ^ ((1 + 2 * p) * m) :=
    QopBounds_num_add hWr1 hL2p (sq_nonneg _) (QopBounds_c_le_W hL ht0 ht1 hWr0.le hWrC hLp)
      QopBounds_c_nonneg le_rfl
  have hfar' := QopBounds_pointwise_far hL ht0 ht1 hA a hfar
  rw [← hm] at hfar'
  have hexp : Real.exp (-((W : ℝ) ^ τ) / 40000) ≤ ((W : ℝ) ^ q)⁻¹ := by
    rw [neg_div, Real.exp_neg]
    exact inv_anti₀ (Real.rpow_pos_of_pos hWr0 _) hWrE
  have hkey : (((L : ℝ) ^ 2) * QopBounds_c L t) ^ m * Real.exp (-((W : ℝ) ^ τ) / 40000)
      ≤ (W : ℝ) ^ (-D) := by
    calc (((L : ℝ) ^ 2) * QopBounds_c L t) ^ m * Real.exp (-((W : ℝ) ^ τ) / 40000)
        ≤ (W : ℝ) ^ ((1 + 2 * p) * m) * ((W : ℝ) ^ q)⁻¹ :=
          mul_le_mul hadd hexp (Real.exp_pos _).le (Real.rpow_nonneg hWr0.le _)
      _ = (W : ℝ) ^ (-D) := by
          rw [← div_eq_mul_inv, ← Real.rpow_sub hWr0]
          congr 1
          rw [hq]
          ring
  have hT0 : 0 ≤ tmax L A := QopBounds_tmax_nonneg A
  have hδ0 : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hWr0.le _
  have hre : ((L : ℝ) ^ 2) ^ m * tmax L A *
      (QopBounds_c L t ^ m * Real.exp (-((W : ℝ) ^ τ) / 40000))
      = tmax L A * ((((L : ℝ) ^ 2) * QopBounds_c L t) ^ m *
        Real.exp (-((W : ℝ) ^ τ) / 40000)) := by
    rw [mul_pow]
    ring
  rw [hre] at hfar'
  have hle : tmax L A * ((((L : ℝ) ^ 2) * QopBounds_c L t) ^ m *
        Real.exp (-((W : ℝ) ^ τ) / 40000)) ≤ tmax L A * (W : ℝ) ^ (-D) :=
    mul_le_mul_of_nonneg_left hkey hT0
  calc ‖Qop L t A a‖ ≤ (W : ℝ) ^ (-D) + tmax L A * (W : ℝ) ^ (-D) :=
        hfar'.trans (add_le_add_right hle _)
    _ ≤ (W : ℝ) ^ (-D) * (2 + tmax L A) := by nlinarith

end RBM.Ind
