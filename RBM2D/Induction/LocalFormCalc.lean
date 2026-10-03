/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM2D.Induction.StoppedEndDefs

/-!
# The local-form calculus of `a-local-form` and the case `m = 4`

Paper: arXiv:2503.07606, Section 5 (`int_K-L+Q2`, `eq:case4_B`, `Def:QtPt`) and Section 7
(`a-local-form`).  The calculus is specific to `d = 2`: the one-dimensional argument uses the
sum-zero Case 2 of `lem:sum_decay`.  Some bounds on `Θ_u`, `ϑ_u`, `S Θ_u`, `ℬ₄` repeat private
lemmas of `RBM2D.Induction.B45`, `RBM2D.Induction.QopBounds` and `RBM2D.Induction.SumZeroQ` under
other names.

Contents (namespace `RBM.Ind`, `variable (d : Sizes)`):
1. `AltLocalFormAt`, the body of `AltLocalForm` (`RBM2D.Induction.StoppedEndDefs`) at one
   `m : Fin 6`, and `altLocalForm_of_at`.
2. The closure lemmas (namespace `RBM.Ind.LocalFormCalc`), for `LocalForm`
   (`RBM2D.Induction.Defs`) and `LabelDecayPT`:
   (a) truncation to `maxDist < ρ`, `ρ = ℓ_u W^{τ₀}/8`: `truncF`, `loc0_trunc_lkF`, the union over
       the `≤ N^k` labels `l1far_PT`, `lkTruncErr` (`𝓛-𝒦`, from `DecayLoopPT`), `kcalTruncErr`
       (`𝒦`, from `KcalDecay`), the polynomial form `lkF` with `eval_lkF`;
   (b) kernel application with truncation: `kerApply`, `loc0_kerApply`, the assembly `asmF`
       (coefficient bound, locality, sum-zero, decay, truncation error) and its stochastic form
       `kernelAssembly_PT` (the truncation error is `O_≺(W^{-D₀})`);
   (c) `𝒫·ϑ̇` as a kernel: `pvdKer`, `sum_pvdKer`, `pvdKer_hyps`, `norm_varthetaDot_le`,
       `norm_varthetaDot_le_decay`;
   (d) products `mulF` (`eval_mulF`, `coef_mulF_le`) and relabelling `comapF`;
   (e) cut contraction `cutKer` (`sum_cutKer`, `cutKer_hyps`);
   (f) `𝒬_u` on the coefficients `qopF`: `eval_qopF`, `sumZero_qopF`, `loc0_qopF`, `coef_qopF_le`;
   (g) error transport `errTransport`.
3. `altLocalFormAt_four`:`ℬ₄ = [𝒬_u, ϴ_{u,σ}](𝓛-𝒦)` for alternating `σ`.  Every `ξ_i = 1`, so
   `ℬ₄ = Σ_c 𝔎_{a,c}(𝓛-𝒦)_c` with the kernel `kerB4` (`commutator_eq_kerB4`, from
   `QopAlgebra` (vii) and `psum_thetaSig_alt`).  `𝔎` depends on `c` only through `c₀`, is
   `≤ 2k(1-u)⁻¹`, and decays like `dec = exp(-·/(20000 ℓ_u))` in `|c₀ - a₀|` and in `maxDist a`
   (`norm_kerB4_le_near`, `norm_kerB4_le_far`).  The local form is `𝒬_u` on the coefficients of
   `𝔎^{tr}(𝓛-𝒦)^{tr}` (`asmF`), `Loc0 (4ρ)`, `4ρ < ℓ_u W^{τ₀}`; the truncation error is
   `O_≺(W^{-D₀})` through `lkTruncErr` and `errTransport`.

Locality: `LocR R F` ("every entry within `R` of some label", `Local τ s ↔ LocR (ℓ_s W^τ)`)
and `Loc0 R F` ("within `R` of the first label `b₀`", the label `𝒫` fixes).  Truncation to
`maxDist b < ρ` turns `LocR R` into `Loc0 (R + 2ρ)` (`loc0_trunc_lkF`); a kernel with
`|c₀ - a₀| < ρ'` adds `2ρ'` (`loc0_kerApply`); `𝒬_u` keeps `Loc0` (`loc0_qopF`).  Radius for
`m = 4`: the truncated loop form is `Loc0 (2ρ)`, the kernel adds `2ρ`, so `Loc0 (4ρ)` and
`4ρ = ℓ_u W^{τ₀}/2 < ℓ_u W^{τ₀}`.

Exponents for `m = 4` (`k ≥ 2`, `K = k`): coefficients `≤ N^{3k+3}` (`C' = 3k+3`); the loop
tensor is `≤ 2N^{k+1}` (`norm_gloop_le_crude` and `exists_norm_Kcal_le_win` with `τ_K = 1`); the
`DecayLoopPT` exponent is `D' = D₀ + (k+3)/c` (`kernelAssembly_PT`, `errTransport` with `C = k+3`,
`N^C ≤ W^{C/c}`); the deterministic tails are `N^{3k+7} exp(-W^{τ₀}/320000) ≤ W^{-D₀}`
eventually (`tail_eventually`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Evol
open scoped NNReal ENNReal

namespace LocalFormCalc

theorem zdist2_neg' (L : ℕ) [NeZero L] (u : Z2 L) : zdist2 L (-u) = zdist2 L u := by
  have h : ∀ x : ZMod L, zdist L (-x) = zdist L x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · have hlt := ZMod.val_lt x
      have hv : (-x).val = L - x.val := by simp [ZMod.neg_val, hx]
      simp only [zdist, hv]
      omega
  simp only [zdist2, Prod.fst_neg, Prod.snd_neg, h]

/-- The triangle inequality for `zdist2` in the form `|x - z| ≤ |x - y| + |y - z|`. -/
theorem zdist2_sub_le (L : ℕ) [NeZero L] (x y z : Z2 L) :
    zdist2 L (x - z) ≤ zdist2 L (x - y) + zdist2 L (y - z) := by
  have h := zdist2_add_le L (x - y) (y - z)
  have e : x - y + (y - z) = x - z := by abel
  rwa [e] at h

theorem zdist2_symm (L : ℕ) [NeZero L] (x y : Z2 L) : zdist2 L (x - y) = zdist2 L (y - x) := by
  rw [← zdist2_neg' L (x - y), neg_sub]

section Algebra

variable {L W : ℕ} [NeZero L] [NeZero W] {k K : ℕ}

/-- The letters of the monomials of a local form: `(x, y, σ)` stands for the entry `G_s(σ)_{xy}`. -/
abbrev Mono (L W : ℕ) [NeZero L] [NeZero W] : Type := Idx L W × Idx L W × Bool

/-- The value of the letter `x = (x, y, σ)` at the matrix `M`: the entry `G_s(σ)_{xy}`. -/
def gFac (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (q : Mono L W) : ℂ :=
  gEntry L W E s M q.2.2 q.1 q.2.1

/-- The evaluation of a form is the polynomial `Σ_j Σ_q coef_{b,j,q} ∏_i G_s(q_i)` (`LocalForm.eval`). -/
theorem eval_eq (F : LocalForm L W k K) (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (b : Fin k → Z2 L) :
    F.eval E s M b = ∑ j : Fin (K + 1), ∑ q : Fin j → Mono L W,
      F.coef b j q * ∏ i : Fin j, gFac E s M (q i) := rfl

/-- The zero form. -/
def zeroF : LocalForm L W k K := ⟨fun _ _ _ => 0⟩

/-- The sum of two forms of the same degree. -/
def addF (F G : LocalForm L W k K) : LocalForm L W k K :=
  ⟨fun b j q => F.coef b j q + G.coef b j q⟩

/-- A scalar multiple. -/
def smulF (r : ℂ) (F : LocalForm L W k K) : LocalForm L W k K :=
  ⟨fun b j q => r * F.coef b j q⟩

/-- The zero form evaluates to `0`. -/
theorem eval_zeroF (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) :
    (zeroF : LocalForm L W k K).eval E s M b = 0 := by
  simp [eval_eq, zeroF]

/-- `eval` is additive. -/
theorem eval_addF (F G : LocalForm L W k K) (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (b : Fin k → Z2 L) : (addF F G).eval E s M b = F.eval E s M b + G.eval E s M b := by
  simp only [eval_eq, addF, add_mul, Finset.sum_add_distrib]

/-- `eval` is homogeneous. -/
theorem eval_smulF (r : ℂ) (F : LocalForm L W k K) (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ)
    (b : Fin k → Z2 L) : (smulF r F).eval E s M b = r * F.eval E s M b := by
  simp only [eval_eq, smulF, Finset.mul_sum, mul_assoc]

/-- The homogeneous form of degree `d ≤ K` with coefficient function `w`. -/
def homF (d : ℕ) (w : (Fin k → Z2 L) → (Fin d → Mono L W) → ℂ) : LocalForm L W k K :=
  ⟨fun b j q => if h : j.val = d then w b (fun i => q (Fin.cast h.symm i)) else 0⟩

/-- A homogeneous form of degree `d ≤ K` evaluates to `Σ_q w_{b,q} ∏_i G_s(q_i)`. -/
theorem eval_homF {d : ℕ} (hd : d ≤ K) (w : (Fin k → Z2 L) → (Fin d → Mono L W) → ℂ)
    (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) :
    (homF (K := K) d w).eval E s M b =
      ∑ q : Fin d → Mono L W, w b q * ∏ i : Fin d, gFac E s M (q i) := by
  rw [eval_eq, Finset.sum_eq_single (⟨d, Nat.lt_succ_of_le hd⟩ : Fin (K + 1))]
  · simp [homF]
  · intro j _ hj
    have : j.val ≠ d := fun h => hj (Fin.ext h)
    simp [homF, this]
  · simp

/-! ### Kernel application -/

/-- Apply a deterministic kernel `𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ` to a form:
`(𝔎F)_a = Σ_c 𝔎 a c F_c`, coefficientwise. -/
def kerApply {k' : ℕ} (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (F : LocalForm L W k K) :
    LocalForm L W k' K :=
  ⟨fun a j q => ∑ c, 𝔎 a c * F.coef c j q⟩

/-- **Closure lemma (b), evaluation**: `kerApply 𝔎 F` evaluates to `Σ_c 𝔎_{a,c} F_c` at every matrix. -/
theorem eval_kerApply {k' : ℕ} (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ)
    (F : LocalForm L W k K) (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Fin k' → Z2 L) :
    (kerApply 𝔎 F).eval E s M a = ∑ c, 𝔎 a c * F.eval E s M c := by
  calc (kerApply 𝔎 F).eval E s M a
      = ∑ j : Fin (K + 1), ∑ q : Fin j → Mono L W, ∑ c, 𝔎 a c *
          (F.coef c j q * ∏ i : Fin j, gFac E s M (q i)) := by
        simp only [eval_eq, kerApply, Finset.sum_mul, mul_assoc]
    _ = ∑ j : Fin (K + 1), ∑ c, ∑ q : Fin j → Mono L W, 𝔎 a c *
          (F.coef c j q * ∏ i : Fin j, gFac E s M (q i)) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ c, ∑ j : Fin (K + 1), ∑ q : Fin j → Mono L W, 𝔎 a c *
          (F.coef c j q * ∏ i : Fin j, gFac E s M (q i)) := Finset.sum_comm
    _ = ∑ c, 𝔎 a c * F.eval E s M c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [eval_eq, Finset.mul_sum]

/-- **Closure lemma (b), coefficients**: if `|coef F| ≤ B` and `Σ_c |𝔎_{a,c}| ≤ B_𝔎`, then `|coef (𝔎F)| ≤ B_𝔎 B`. -/
theorem coef_kerApply_le {k' : ℕ} (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ)
    (F : LocalForm L W k K) {B B𝔎 : ℝ} (hB : 0 ≤ B) (hF : ∀ c j q, ‖F.coef c j q‖ ≤ B)
    (h𝔎 : ∀ a, ∑ c, ‖𝔎 a c‖ ≤ B𝔎) (a : Fin k' → Z2 L) (j : Fin (K + 1))
    (q : Fin j → Mono L W) : ‖(kerApply 𝔎 F).coef a j q‖ ≤ B𝔎 * B := by
  simp only [kerApply]
  calc ‖∑ c, 𝔎 a c * F.coef c j q‖ ≤ ∑ c, ‖𝔎 a c * F.coef c j q‖ := norm_sum_le _ _
    _ ≤ ∑ c, ‖𝔎 a c‖ * B := Finset.sum_le_sum fun c _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hF c j q) (norm_nonneg _)
    _ = (∑ c, ‖𝔎 a c‖) * B := by rw [Finset.sum_mul]
    _ ≤ B𝔎 * B := mul_le_mul_of_nonneg_right (h𝔎 a) hB

/-! ### Locality -/

/-- `LocR R F`: every entry of a monomial with a non-zero coefficient is within `R` of some label
(the predicate underlying `LocalForm.Local`, `Local τ s ↔ LocR (ℓ_s W^τ)`). -/
def LocR (R : ℝ) (F : LocalForm L W k K) : Prop :=
  ∀ b j q, F.coef b j q ≠ 0 → ∀ i, ∃ m : Fin k,
    ((zdist2 L ((splitEquiv L W (q i).1).1 - b m) +
        zdist2 L ((splitEquiv L W (q i).2.1).1 - b m) : ℕ) : ℝ) < R

/-- `Loc0 R F`: every entry of a monomial with a non-zero coefficient is within `R` of the label
`b_0` (the first label, the one that `𝒫` fixes). -/
def Loc0 [NeZero k] (R : ℝ) (F : LocalForm L W k K) : Prop :=
  ∀ b j q, F.coef b j q ≠ 0 → ∀ i,
    ((zdist2 L ((splitEquiv L W (q i).1).1 - b 0) +
        zdist2 L ((splitEquiv L W (q i).2.1).1 - b 0) : ℕ) : ℝ) < R

/-- `Loc0 R` implies `LocR R'` for `R ≤ R'` (the first label is one of the labels). -/
theorem Loc0.locR [NeZero k] {R R' : ℝ} {F : LocalForm L W k K} (h : Loc0 R F) (hR : R ≤ R') :
    LocR R' F := fun b j q hq i => ⟨0, lt_of_lt_of_le (h b j q hq i) hR⟩

/-- `Loc0 R` with `R ≤ ℓ_s W^τ` gives `LocalForm.Local τ s`. -/
theorem Loc0.local [NeZero k] {R : ℝ} {F : LocalForm L W k K} (h : Loc0 R F) (τ s : ℝ)
    (hR : R ≤ ellT L s * (W : ℝ) ^ τ) : F.Local τ s := h.locR hR

/-- **Kernel locality** (closure lemma (b)): if `F` is local around the first label with radius `R`
and `𝔎 a c ≠ 0` forces `|c_0 - a_0| < ρ'`, then `𝔎F` is local around `a_0` with radius `R + 2ρ'`. -/
theorem loc0_kerApply {k' : ℕ} [NeZero k] [NeZero k'] {R ρ' : ℝ}
    (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (F : LocalForm L W k K) (hF : Loc0 R F)
    (h𝔎 : ∀ a c, 𝔎 a c ≠ 0 → ((zdist2 L (c 0 - a 0) : ℕ) : ℝ) < ρ') :
    Loc0 (R + 2 * ρ') (kerApply 𝔎 F) := by
  intro a j q hq i
  simp only [kerApply] at hq
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  have h1 : 𝔎 a c ≠ 0 := left_ne_zero_of_mul hc
  have h2 : F.coef c j q ≠ 0 := right_ne_zero_of_mul hc
  have hFi := hF c j q h2 i
  have hd := h𝔎 a c h1
  have t1 := zdist2_sub_le L (splitEquiv L W (q i).1).1 (c 0) (a 0)
  have t2 := zdist2_sub_le L (splitEquiv L W (q i).2.1).1 (c 0) (a 0)
  have t1' : ((zdist2 L ((splitEquiv L W (q i).1).1 - a 0) : ℕ) : ℝ) ≤
      (zdist2 L ((splitEquiv L W (q i).1).1 - c 0) : ℝ) + (zdist2 L (c 0 - a 0) : ℝ) := by
    exact_mod_cast t1
  have t2' : ((zdist2 L ((splitEquiv L W (q i).2.1).1 - a 0) : ℕ) : ℝ) ≤
      (zdist2 L ((splitEquiv L W (q i).2.1).1 - c 0) : ℝ) + (zdist2 L (c 0 - a 0) : ℝ) := by
    exact_mod_cast t2
  push_cast at hFi ⊢
  linarith

/-! ### Truncation in the labels -/

/-- Truncation of the label tensor to `maxDist b < ρ` (closure lemma (a), the deterministic part). -/
def truncF (ρ : ℝ) (F : LocalForm L W k K) : LocalForm L W k K :=
  ⟨fun b j q => if (KLoop.maxDist L b : ℝ) < ρ then F.coef b j q else 0⟩

/-- Truncation to `maxDist b < ρ` is pointwise: `eval (F^{tr}) b = 1(maxDist b < ρ) eval F b`. -/
theorem eval_truncF (ρ : ℝ) (F : LocalForm L W k K) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) :
    (truncF ρ F).eval E s M b = if (KLoop.maxDist L b : ℝ) < ρ then F.eval E s M b else 0 := by
  by_cases h : (KLoop.maxDist L b : ℝ) < ρ
  · simp [eval_eq, truncF, h]
  · simp [eval_eq, truncF, h]

/-- Every pairwise distance is at most `maxDist`. -/
theorem zdist2_le_maxDist {k : ℕ} (a : Fin k → Z2 L) (i j : Fin k) :
    zdist2 L (a i - a j) ≤ KLoop.maxDist L a :=
  Finset.le_sup (f := fun p : Fin k × Fin k => zdist2 L (a p.1 - a p.2)) (Finset.mem_univ (i, j))

/-- Truncation does not increase the coefficients. -/
theorem coef_truncF_le (ρ : ℝ) (F : LocalForm L W k K) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ c j q, ‖F.coef c j q‖ ≤ B) (c : Fin k → Z2 L) (j : Fin (K + 1)) (q : Fin j → Mono L W) :
    ‖(truncF ρ F).coef c j q‖ ≤ B := by
  simp only [truncF]
  split_ifs
  · exact hF c j q
  · simpa using hB

/-! ### Products and relabelling (closure lemma (d)) -/

/-- The product of two forms in the same labels (degrees add): a monomial of length `j` is split
into its first `j₁` and last `j₂` letters, `j₁ + j₂ = j`. -/
def mulF {K₁ K₂ : ℕ} (F : LocalForm L W k K₁) (G : LocalForm L W k K₂) :
    LocalForm L W k (K₁ + K₂) :=
  ⟨fun b j q => ∑ j₁ : Fin (K₁ + 1), ∑ j₂ : Fin (K₂ + 1),
      if h : j₁.val + j₂.val = j.val then
        F.coef b j₁ (fun i => q ⟨i.val, by omega⟩) *
          G.coef b j₂ (fun i => q ⟨j₁.val + i.val, by omega⟩)
      else 0⟩

/-- Splitting a monomial of length `j₁ + j₂` into its first `j₁` and last `j₂` letters. -/
theorem sum_split {j₁ j₂ : ℕ} (f : (Fin j₁ → Mono L W) → (Fin j₂ → Mono L W) → ℂ)
    (g : Mono L W → ℂ) :
    ∑ q : Fin (j₁ + j₂) → Mono L W,
        f (fun i => q (Fin.castAdd j₂ i)) (fun i => q (Fin.natAdd j₁ i)) * ∏ i, g (q i) =
      ∑ q₁ : Fin j₁ → Mono L W, ∑ q₂ : Fin j₂ → Mono L W,
        f q₁ q₂ * ((∏ i, g (q₁ i)) * ∏ i, g (q₂ i)) := by
  rw [← (Fin.appendEquiv j₁ j₂).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun q₂ _ => ?_
  simp [Fin.appendEquiv, Fin.prod_univ_add]

/-- **Closure lemma (d), evaluation**: `(F·G)_b = F_b G_b`; the degrees add (`K₁ + K₂`). -/
theorem eval_mulF {K₁ K₂ : ℕ} (F : LocalForm L W k K₁) (G : LocalForm L W k K₂) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) :
    (mulF F G).eval E s M b = F.eval E s M b * G.eval E s M b := by
  have key : ∀ (j₁ : Fin (K₁ + 1)) (j₂ : Fin (K₂ + 1)),
      (∑ j : Fin (K₁ + K₂ + 1), ∑ q : Fin j → Mono L W,
        (if h : j₁.val + j₂.val = j.val then
          F.coef b j₁ (fun i => q ⟨i.val, by omega⟩) *
            G.coef b j₂ (fun i => q ⟨j₁.val + i.val, by omega⟩)
        else 0) * ∏ i : Fin j, gFac E s M (q i)) =
      ∑ q₁ : Fin j₁ → Mono L W, ∑ q₂ : Fin j₂ → Mono L W,
        F.coef b j₁ q₁ * G.coef b j₂ q₂ *
          ((∏ i, gFac E s M (q₁ i)) * ∏ i, gFac E s M (q₂ i)) := by
    intro j₁ j₂
    have hlt : j₁.val + j₂.val < K₁ + K₂ + 1 := by omega
    rw [Finset.sum_eq_single (⟨j₁.val + j₂.val, hlt⟩ : Fin (K₁ + K₂ + 1))]
    · have hpos : j₁.val + j₂.val = (⟨j₁.val + j₂.val, hlt⟩ : Fin (K₁ + K₂ + 1)).val := rfl
      refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_)
        (sum_split (L := L) (W := W) (fun q₁ q₂ => F.coef b j₁ q₁ * G.coef b j₂ q₂)
          (gFac E s M))
      split_ifs
      rfl
    · intro j _ hj
      have hne : ¬ (j₁.val + j₂.val = j.val) := fun h => hj (Fin.ext h.symm)
      simp [hne]
    · simp
  calc (mulF F G).eval E s M b
      = ∑ j : Fin (K₁ + K₂ + 1), ∑ q : Fin j → Mono L W,
          ∑ j₁ : Fin (K₁ + 1), ∑ j₂ : Fin (K₂ + 1),
          (if h : j₁.val + j₂.val = j.val then
            F.coef b j₁ (fun i => q ⟨i.val, by omega⟩) *
              G.coef b j₂ (fun i => q ⟨j₁.val + i.val, by omega⟩)
          else 0) * ∏ i : Fin j, gFac E s M (q i) := by
        simp only [eval_eq, mulF, Finset.sum_mul]
    _ = ∑ j₁ : Fin (K₁ + 1), ∑ j₂ : Fin (K₂ + 1), ∑ j : Fin (K₁ + K₂ + 1), ∑ q : Fin j → Mono L W,
          (if h : j₁.val + j₂.val = j.val then
            F.coef b j₁ (fun i => q ⟨i.val, by omega⟩) *
              G.coef b j₂ (fun i => q ⟨j₁.val + i.val, by omega⟩)
          else 0) * ∏ i : Fin j, gFac E s M (q i) := by
        have e1 : ∀ j : Fin (K₁ + K₂ + 1), ∀ q : Fin j → Mono L W,
            (∑ j₁ : Fin (K₁ + 1), ∑ j₂ : Fin (K₂ + 1),
              (if h : j₁.val + j₂.val = j.val then
                F.coef b j₁ (fun i => q ⟨i.val, by omega⟩) *
                  G.coef b j₂ (fun i => q ⟨j₁.val + i.val, by omega⟩)
              else 0) * ∏ i : Fin j, gFac E s M (q i)) = _ := fun j q => rfl
        calc _ = ∑ j : Fin (K₁ + K₂ + 1), ∑ j₁ : Fin (K₁ + 1), ∑ j₂ : Fin (K₂ + 1),
              ∑ q : Fin j → Mono L W,
              (if h : j₁.val + j₂.val = j.val then
                F.coef b j₁ (fun i => q ⟨i.val, by omega⟩) *
                  G.coef b j₂ (fun i => q ⟨j₁.val + i.val, by omega⟩)
              else 0) * ∏ i : Fin j, gFac E s M (q i) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j₁ _ => ?_
              rw [Finset.sum_comm]
          _ = _ := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j₁ _ => ?_
              rw [Finset.sum_comm]
    _ = ∑ j₁ : Fin (K₁ + 1), ∑ j₂ : Fin (K₂ + 1), ∑ q₁ : Fin j₁ → Mono L W,
          ∑ q₂ : Fin j₂ → Mono L W, F.coef b j₁ q₁ * G.coef b j₂ q₂ *
            ((∏ i, gFac E s M (q₁ i)) * ∏ i, gFac E s M (q₂ i)) :=
        Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => key j₁ j₂
    _ = F.eval E s M b * G.eval E s M b := by
        simp only [eval_eq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
        refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun q₂ _ => ?_
        ring

/-- **Closure lemma (d), coefficients**: `|coef (F·G)| ≤ (K₁+1)(K₂+1) B₁ B₂`. -/
theorem coef_mulF_le {K₁ K₂ : ℕ} (F : LocalForm L W k K₁) (G : LocalForm L W k K₂) {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hF : ∀ c j q, ‖F.coef c j q‖ ≤ B₁)
    (hG : ∀ c j q, ‖G.coef c j q‖ ≤ B₂) (b : Fin k → Z2 L) (j : Fin (K₁ + K₂ + 1))
    (q : Fin j → Mono L W) :
    ‖(mulF F G).coef b j q‖ ≤ ((K₁ + 1 : ℕ) : ℝ) * ((K₂ + 1 : ℕ) : ℝ) * (B₁ * B₂) := by
  simp only [mulF]
  calc ‖∑ j₁ : Fin (K₁ + 1), ∑ j₂ : Fin (K₂ + 1),
        (if h : j₁.val + j₂.val = j.val then
          F.coef b j₁ (fun i => q ⟨i.val, by omega⟩) *
            G.coef b j₂ (fun i => q ⟨j₁.val + i.val, by omega⟩)
        else 0)‖
      ≤ ∑ j₁ : Fin (K₁ + 1), ∑ j₂ : Fin (K₂ + 1), B₁ * B₂ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j₁ _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j₂ _ => ?_)
        split_ifs
        · rw [norm_mul]; exact mul_le_mul (hF _ _ _) (hG _ _ _) (norm_nonneg _) hB₁
        · simpa using mul_nonneg hB₁ hB₂
    _ = ((K₁ + 1 : ℕ) : ℝ) * ((K₂ + 1 : ℕ) : ℝ) * (B₁ * B₂) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- Relabelling: `(comapF f F)_{b'} = F_{b' ∘ f}` for `f : Fin k → Fin k'` (used to insert a form in
the labels `b ∘ f` into a larger label set; closure lemma (d)/(e)). -/
def comapF {k' : ℕ} (f : Fin k → Fin k') (F : LocalForm L W k K) : LocalForm L W k' K :=
  ⟨fun b j q => F.coef (fun m => b (f m)) j q⟩

/-- Relabelling: `(comap f F)_{b'} = F_{b'∘f}`. -/
theorem eval_comapF {k' : ℕ} (f : Fin k → Fin k') (F : LocalForm L W k K) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k' → Z2 L) :
    (comapF f F).eval E s M b = F.eval E s M (fun m => b (f m)) := rfl

/-! ### `𝒬_u` on the coefficients (closure lemma (f)) -/

/-- The kernel of `𝒬_u` (`Def:QtPt`): `(𝒬_uX)_a = Σ_c 𝔎_{a,c} X_c`. -/
def qopKernel (L : ℕ) [NeZero L] {k : ℕ} [NeZero k] (u : ℝ) (a c : Fin k → Z2 L) : ℂ :=
  (if c = a then 1 else 0) - (if c 0 = a 0 then vartheta L u a else 0)

/-- `𝒬_u` is the kernel operator `qopKernel`. -/
theorem qopKernel_sum [NeZero k] (u : ℝ) (X : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    ∑ c, qopKernel L u a c * X c = Qop L u X a := by
  unfold qopKernel Qop Psum
  have h1 : ∑ c, (if c = a then (1 : ℂ) else 0) * X c = X a := by simp
  have h2 : ∑ c, (if c 0 = a 0 then vartheta L u a else 0) * X c =
      (∑ c ∈ Finset.univ.filter (fun c : Fin k → Z2 L => c 0 = a 0), X c) * vartheta L u a := by
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> simp [mul_comm]
  simp only [sub_mul, Finset.sum_sub_distrib, h1, h2]

/-- `kerApply (qopKernel u) F` evaluates to `𝒬_u` of the evaluation of `F`. -/
theorem eval_kerApply_qop [NeZero k] (u : ℝ) (F : LocalForm L W k K) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Fin k → Z2 L) :
    (kerApply (qopKernel L u) F).eval E s M a = Qop L u (F.eval E s M) a := by
  rw [eval_kerApply, qopKernel_sum]

/-- `𝒬_u` on the coefficients of a form (closure lemma (f)). -/
def qopF [NeZero k] (u : ℝ) (F : LocalForm L W k K) : LocalForm L W k K :=
  kerApply (qopKernel L u) F

/-- **Closure lemma (f), evaluation**: `qopF u F` evaluates to `𝒬_u (F_·)` at every matrix. -/
theorem eval_qopF [NeZero k] (u : ℝ) (F : LocalForm L W k K) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (a : Fin k → Z2 L) :
    (qopF u F).eval E s M a = Qop L u (F.eval E s M) a := eval_kerApply_qop u F E s M a

/-- `𝒬_u F` is sum-zero for every matrix `M` (`QopAlgebra` (ii)). -/
theorem sumZero_qopF [NeZero k] (hL : 3 ≤ L) (hk : 2 ≤ k) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (F : LocalForm L W k K) (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) :
    SumZero L (fun b => (qopF u F).eval E s M b) := by
  intro a₁
  have h := (qopAlgebra L hL k hk u hu0 hu1).2.1 (F.eval E s M) a₁
  unfold Psum at h
  simp only [eval_qopF]
  exact h

/-- `𝒬_u` preserves the locality around the first label, with the same radius. -/
theorem loc0_qopF [NeZero k] {R : ℝ} (u : ℝ) (F : LocalForm L W k K) (hF : Loc0 R F) :
    Loc0 R (qopF u F) := by
  intro a j q hq i
  simp only [qopF, kerApply] at hq
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  have h1 : qopKernel L u a c ≠ 0 := left_ne_zero_of_mul hc
  have h2 : F.coef c j q ≠ 0 := right_ne_zero_of_mul hc
  have h0 : c 0 = a 0 := by
    by_contra hne
    apply h1
    have hne' : c ≠ a := fun h => hne (by rw [h])
    simp [qopKernel, hne, hne']
  have := hF c j q h2 i
  rwa [h0] at this

/-- `|(Z_L²)^k| = (L²)^k`. -/
theorem card_labels (k : ℕ) : (Fintype.card (Fin k → Z2 L) : ℝ) = ((L : ℝ) ^ 2) ^ k := by
  simp [Z2, ZMod.card]
  ring

/-- `Σ_c |qopKernel_{a,c}| ≤ 1 + |(Z_L²)^k| |ϑ_a|`. -/
theorem sum_norm_qopKernel_le [NeZero k] (u : ℝ) (a : Fin k → Z2 L) :
    ∑ c, ‖qopKernel L u a c‖ ≤ 1 + ((L : ℝ) ^ 2) ^ k * ‖vartheta L u a‖ := by
  have h : ∀ c : Fin k → Z2 L, ‖qopKernel L u a c‖ ≤ (if c = a then (1 : ℝ) else 0) + ‖vartheta L u a‖ := by
    intro c
    unfold qopKernel
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ?_ ?_
    · split_ifs <;> simp
    · split_ifs <;> simp
  calc ∑ c, ‖qopKernel L u a c‖ ≤ ∑ c : Fin k → Z2 L, ((if c = a then (1 : ℝ) else 0) + ‖vartheta L u a‖) :=
        Finset.sum_le_sum fun c _ => h c
    _ = 1 + ((L : ℝ) ^ 2) ^ k * ‖vartheta L u a‖ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ a (fun _ => (1 : ℝ)),
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_labels]
        simp

/-- **Closure lemma (f), coefficients**: `|coef (𝒬_u F)| ≤ (1 + |{a}|) B` if `|ϑ| ≤ 1` and `|coef F| ≤ B`. -/
theorem coef_qopF_le [NeZero k] (u : ℝ) (F : LocalForm L W k K) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ c j q, ‖F.coef c j q‖ ≤ B) (hϑ : ∀ a : Fin k → Z2 L, ‖vartheta L u a‖ ≤ 1)
    (a : Fin k → Z2 L) (j : Fin (K + 1)) (q : Fin j → Mono L W) :
    ‖(qopF u F).coef a j q‖ ≤ (1 + ((L : ℝ) ^ 2) ^ k) * B := by
  refine coef_kerApply_le (qopKernel L u) F hB hF (B𝔎 := 1 + ((L : ℝ) ^ 2) ^ k) (fun a' => ?_) a j q
  refine (sum_norm_qopKernel_le u a').trans ?_
  have : ((L : ℝ) ^ 2) ^ k * ‖vartheta L u a'‖ ≤ ((L : ℝ) ^ 2) ^ k * 1 :=
    mul_le_mul_of_nonneg_left (hϑ a') (by positivity)
  linarith

end Algebra

section LoopExpansion

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- One step of the path expansion of a loop word: `(G_s E_b R)_{xy} = Σ_p G_s(x,p) E_b(p,p) R_{py}`. -/
theorem gloopProd_cons_apply {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ} {z : ℂ} (s : Bool)
    (b : Z2 L) (σl : List Bool) (al : List (Z2 L)) (x y : BlockIndex L W) :
    gloopProd L W H z ⟨s :: σl, b :: al⟩ x y =
      ∑ p : BlockIndex L W, Gsig H z s x p * Eblk L W b p p * gloopProd L W H z ⟨σl, al⟩ p y := by
  rw [gloopProd_cons]
  simp only [Matrix.mul_apply, Eblk_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [mul_assoc]

/-- **The open-path expansion of a loop word**: the `(x, y)` entry of `∏ᵢ G_{σᵢ} E_{aᵢ}` is the sum
over paths `π₀ = x, π₁, …, π_n = y` of `∏ᵢ G_{σᵢ}(π_i, π_{i+1}) E_{aᵢ}(π_{i+1}, π_{i+1})`. -/
theorem gloopProd_ofFn_apply (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) :
    ∀ (n : ℕ) (σ : Fin n → Bool) (a : Fin n → Z2 L) (x y : BlockIndex L W),
      gloopProd L W H z ⟨List.ofFn σ, List.ofFn a⟩ x y =
        ∑ π : Fin (n + 1) → BlockIndex L W,
          (if π 0 = x ∧ π (Fin.last n) = y then (1 : ℂ) else 0) *
            ∏ i : Fin n, (Gsig H z (σ i) (π i.castSucc) (π i.succ) *
              Eblk L W (a i) (π i.succ) (π i.succ))
  | 0, σ, a, x, y => by
    simp only [List.ofFn_zero, gloopProd_nil, Matrix.one_apply, Finset.univ_eq_empty,
      Finset.prod_empty, mul_one]
    rw [← (Equiv.funUnique (Fin 1) (BlockIndex L W)).symm.sum_comp]
    by_cases hxy : x = y
    · subst hxy; simp [Fin.last]
    · simp only [hxy, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun v _ => ?_
      have : ¬ (v = x ∧ v = y) := fun ⟨h1, h2⟩ => hxy (h1.symm.trans h2)
      simp [Fin.last, this]
  | n + 1, σ, a, x, y => by
    rw [List.ofFn_succ, List.ofFn_succ, gloopProd_cons_apply]
    simp_rw [gloopProd_ofFn_apply H z n (fun i => σ i.succ) (fun i => a i.succ)]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => BlockIndex L W)).sum_comp]
    conv_rhs => rw [Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.castSucc_zero]
    -- collapse the left `π₀` on the right and the middle point `p` on the left
    have hR : ∀ π' : Fin (n + 1) → BlockIndex L W,
        (∑ π₀ : BlockIndex L W,
          (if π₀ = x ∧ (Fin.cons π₀ π' : Fin (n + 2) → BlockIndex L W) (Fin.last (n + 1)) = y
              then (1 : ℂ) else 0) *
            (Gsig H z (σ 0) π₀ (π' 0) * Eblk L W (a 0) (π' 0) (π' 0) *
              ∏ i : Fin n, Gsig H z (σ i.succ)
                  ((Fin.cons π₀ π' : Fin (n + 2) → BlockIndex L W) i.succ.castSucc) (π' i.succ) *
                Eblk L W (a i.succ) (π' i.succ) (π' i.succ))) =
          (if π' (Fin.last n) = y then (1 : ℂ) else 0) *
            (Gsig H z (σ 0) x (π' 0) * Eblk L W (a 0) (π' 0) (π' 0) *
              ∏ i : Fin n, Gsig H z (σ i.succ) (π' i.castSucc) (π' i.succ) *
                Eblk L W (a i.succ) (π' i.succ) (π' i.succ)) := by
      intro π'
      rw [Finset.sum_eq_single x]
      · have h1 : (Fin.cons x π' : Fin (n + 2) → BlockIndex L W) (Fin.last (n + 1)) =
            π' (Fin.last n) := by
          rw [← Fin.succ_last]; simp
        have h2 : ∀ i : Fin n, (Fin.cons x π' : Fin (n + 2) → BlockIndex L W) i.succ.castSucc =
            π' i.castSucc := by
          intro i
          rw [← Fin.succ_castSucc]; simp
        simp only [h1, h2, true_and]
      · intro π₀ _ h0
        simp [h0]
      · simp
    have hL : ∀ π' : Fin (n + 1) → BlockIndex L W,
        (∑ p : BlockIndex L W, Gsig H z (σ 0) x p * Eblk L W (a 0) p p *
          ((if π' 0 = p ∧ π' (Fin.last n) = y then (1 : ℂ) else 0) *
            ∏ i : Fin n, Gsig H z (σ i.succ) (π' i.castSucc) (π' i.succ) *
              Eblk L W (a i.succ) (π' i.succ) (π' i.succ))) =
          (if π' (Fin.last n) = y then (1 : ℂ) else 0) *
            (Gsig H z (σ 0) x (π' 0) * Eblk L W (a 0) (π' 0) (π' 0) *
              ∏ i : Fin n, Gsig H z (σ i.succ) (π' i.castSucc) (π' i.succ) *
                Eblk L W (a i.succ) (π' i.succ) (π' i.succ)) := by
      intro π'
      rw [Finset.sum_eq_single (π' 0)]
      · simp only [true_and]; ring
      · intro p _ hp
        have : ¬ (π' 0 = p) := fun h => hp h.symm
        simp [this]
      · simp
    calc _ = ∑ π' : Fin (n + 1) → BlockIndex L W, (if π' (Fin.last n) = y then (1 : ℂ) else 0) *
            (Gsig H z (σ 0) x (π' 0) * Eblk L W (a 0) (π' 0) (π' 0) *
              ∏ i : Fin n, Gsig H z (σ i.succ) (π' i.castSucc) (π' i.succ) *
                Eblk L W (a i.succ) (π' i.succ) (π' i.succ)) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun π' _ => hL π'
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun π' _ => (hR π').symm

/-- The cyclic predecessor `i ↦ i - 1` on `Fin k`. -/
def prvK (k : ℕ) [NeZero k] (i : Fin k) : Fin k :=
  ⟨(i.val + (k - 1)) % k, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne k))⟩

/-- `prvK` sends `0` to the last index. -/
theorem prvK_zero (m : ℕ) : prvK (m + 1) 0 = Fin.last m := by
  ext
  simp [prvK, Fin.last]

/-- `prvK` sends `j+1` to `j`. -/
theorem prvK_succ (m : ℕ) (j : Fin m) : prvK (m + 1) j.succ = j.castSucc := by
  ext
  have h : j.val + 1 + (m + 1 - 1) = j.val + (m + 1) := by omega
  simp only [prvK, Fin.val_succ, Fin.val_castSucc, h, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by have := j.isLt; omega)

/-- `(cons v p)(i.castSucc) = p (i - 1)` when `v = p (last)`: the closing of a cyclic path. -/
theorem cons_castSucc_prvK {X : Type*} (m : ℕ) (p : Fin (m + 1) → X) (i : Fin (m + 1)) :
    (Fin.cons (p (Fin.last m)) p : Fin (m + 2) → X) i.castSucc = p (prvK (m + 1) i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [prvK_zero]; simp
  · rw [prvK_succ, ← Fin.succ_castSucc]
    simp

/-- **The cyclic path expansion of a loop**: `𝓛_{σ,c} = Σ_{p : Fin k → X} ∏ᵢ G_{σᵢ}(p_{i-1}, pᵢ) E_{cᵢ}(pᵢ, pᵢ)`. -/
theorem gloop_loopOf_eq {k : ℕ} [NeZero k] (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ)
    (σ : Fin k → Bool) (c : Fin k → Z2 L) :
    gloop L W H z (loopOf σ c) =
      ∑ p : Fin k → BlockIndex L W, ∏ i : Fin k,
        (Gsig H z (σ i) (p (prvK k i)) (p i) * Eblk L W (c i) (p i) (p i)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  have h1 : gloop L W H z (loopOf σ c) =
      ∑ x : BlockIndex L W, gloopProd L W H z ⟨List.ofFn σ, List.ofFn c⟩ x x := by
    rfl
  rw [h1]
  simp_rw [gloopProd_ofFn_apply H z (m + 1) σ c]
  rw [Finset.sum_comm]
  have h2 : ∀ π : Fin (m + 2) → BlockIndex L W,
      (∑ x : BlockIndex L W, (if π 0 = x ∧ π (Fin.last (m + 1)) = x then (1 : ℂ) else 0) *
        ∏ i : Fin (m + 1), (Gsig H z (σ i) (π i.castSucc) (π i.succ) *
          Eblk L W (c i) (π i.succ) (π i.succ))) =
        (if π 0 = π (Fin.last (m + 1)) then (1 : ℂ) else 0) *
          ∏ i : Fin (m + 1), (Gsig H z (σ i) (π i.castSucc) (π i.succ) *
            Eblk L W (c i) (π i.succ) (π i.succ)) := by
    intro π
    rw [Finset.sum_eq_single (π 0)]
    · by_cases h : π 0 = π (Fin.last (m + 1))
      · simp [h]
      · have h' : ¬ π (Fin.last (m + 1)) = π 0 := fun e => h e.symm
        simp [h, h']
    · intro x _ hx
      have : ¬ (π 0 = x ∧ π (Fin.last (m + 1)) = x) := fun ⟨h1, _⟩ => hx h1.symm
      simp [this]
    · simp
  simp_rw [h2]
  rw [← (Fin.consEquiv (fun _ : Fin (m + 2) => BlockIndex L W)).sum_comp]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single (p (Fin.last m))]
  · have e0 : (Fin.cons (p (Fin.last m)) p : Fin (m + 2) → BlockIndex L W) 0 = p (Fin.last m) := rfl
    have e1 : (Fin.cons (p (Fin.last m)) p : Fin (m + 2) → BlockIndex L W) (Fin.last (m + 1)) =
        p (Fin.last m) := by
      rw [← Fin.succ_last]; simp
    simp only [e0, e1, ite_true, one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [cons_castSucc_prvK]
    simp
  · intro π₀ _ hπ
    have e0 : (Fin.cons π₀ p : Fin (m + 2) → BlockIndex L W) 0 = π₀ := rfl
    have e1 : (Fin.cons π₀ p : Fin (m + 2) → BlockIndex L W) (Fin.last (m + 1)) =
        p (Fin.last m) := by
      rw [← Fin.succ_last]; simp
    simp [e0, e1, hπ]
  · simp

/-- `G(σ)` of the block matrix is the entry `gEntry` of the fine matrix at the split indices. -/
theorem Gsig_blockMat (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool) (x y : Idx L W) :
    Gsig (blockMat M) (spectralZ E u) σ (splitEquiv L W x) (splitEquiv L W y) =
      gEntry L W E u M σ x y := by
  unfold Gsig gEntry green blockMat
  have h : ∀ z' : ℂ, M.submatrix (splitEquiv L W).symm (splitEquiv L W).symm -
      z' • (1 : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) =
      (M - z' • (1 : Matrix (Idx L W) (Idx L W) ℂ)).submatrix (splitEquiv L W).symm
        (splitEquiv L W).symm := by
    intro z'
    ext p q
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hpq : p = q
    · subst hpq; simp
    · have : (splitEquiv L W).symm p ≠ (splitEquiv L W).symm q :=
        fun h => hpq ((splitEquiv L W).symm.injective h)
      simp [hpq, this]
  simp only [h, Matrix.inv_submatrix_equiv, Matrix.submatrix_apply, Equiv.symm_apply_apply]

/-- The monomial of a loop path `p`: the letters `(p_{i-1}, p_i, σ_i)`. -/
def qOf {k : ℕ} [NeZero k] (σ : Fin k → Bool) (p : Fin k → Idx L W) : Fin k → Mono L W :=
  fun i => (p (prvK k i), p i, σ i)

/-- The weight `∏ᵢ E_{cᵢ}(pᵢ, pᵢ)` of a loop path. -/
def loopW {k : ℕ} (c : Fin k → Z2 L) (p : Fin k → Idx L W) : ℂ :=
  ∏ i, Eblk L W (c i) (splitEquiv L W (p i)) (splitEquiv L W (p i))

/-- **The loop `𝓛_{σ,c}` as a local form** of degree `k`: a monomial per path, the coefficient of
the monomial `qOf σ p` being the block weight `∏ᵢ E_{cᵢ}(pᵢ, pᵢ) = W^{-2k} ∏ᵢ 1(pᵢ ∈ block cᵢ)`. -/
def loopF {k : ℕ} [NeZero k] (σ : Fin k → Bool) : LocalForm L W k k :=
  homF k (fun c q => ∑ p : Fin k → Idx L W, if q = qOf σ p then loopW c p else 0)

/-- **The loop `𝓛_{σ,c}` as a local form**: `loopF σ` evaluates to `gloop` (the trace of `∏ G_{σ_i} E_{c_i}`) at every matrix. -/
theorem eval_loopF {k : ℕ} [NeZero k] (σ : Fin k → Bool) (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (c : Fin k → Z2 L) :
    (loopF σ).eval E u M c = gloop L W (blockMat M) (spectralZ E u) (loopOf σ c) := by
  rw [gloop_loopOf_eq]
  unfold loopF
  rw [eval_homF le_rfl]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ p : Fin k → Idx L W,
      (∑ q : Fin k → Mono L W, (if q = qOf σ p then loopW c p else 0) *
          ∏ i : Fin k, gFac E u M (q i)) =
        ∏ i : Fin k, (gEntry L W E u M (σ i) (p (prvK k i)) (p i) *
          Eblk L W (c i) (splitEquiv L W (p i)) (splitEquiv L W (p i))) := by
    intro p
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (qOf σ p)]
    simp only [Finset.mem_univ, ite_true]
    unfold loopW
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [gFac, qOf]
    ring
  simp_rw [h1]
  let e : (Fin k → Idx L W) ≃ (Fin k → BlockIndex L W) :=
    Equiv.piCongrRight (fun _ => splitEquiv L W)
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun p _ => Finset.prod_congr rfl fun i _ => ?_
  simp only [e, Equiv.piCongrRight_apply, Pi.map_apply, Gsig_blockMat]

/-- The constant (degree `0`) form `b ↦ v b` (used for `𝒦`). -/
def constF {k K : ℕ} (v : (Fin k → Z2 L) → ℂ) : LocalForm L W k K :=
  homF 0 (fun b _ => v b)

/-- The constant form evaluates to its value. -/
theorem eval_constF {k K : ℕ} (v : (Fin k → Z2 L) → ℂ) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) :
    (constF (K := K) v : LocalForm L W k K).eval E s M b = v b := by
  unfold constF
  rw [eval_homF (Nat.zero_le K)]
  simp

/-- **The tensor `𝓛 - 𝒦` (`lkTensor`) as a local form** of degree `k`: the loop polynomial `loopF`
minus the constant `𝒦`. -/
def lkF {k : ℕ} [NeZero k] (σ : Fin k → Bool) (E u : ℝ) : LocalForm L W k k :=
  addF (loopF σ) (smulF (-1) (constF (fun b => KLoop.Kcal L W E u (loopOf σ b))))

/-- **The tensor `𝓛 - 𝒦` as a local form**: `lkF σ E u` evaluates to `lkTensor` at every matrix. -/
theorem eval_lkF {k : ℕ} [NeZero k] (σ : Fin k → Bool) (E u : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) :
    (lkF σ E u : LocalForm L W k k).eval E u M b = lkTensor L W E u M σ b := by
  unfold lkF
  rw [eval_addF, eval_smulF, eval_constF, eval_loopF]
  unfold lkTensor LKf LLf
  ring

/-- The monomial of a loop path determines the path. -/
theorem qOf_injective {k : ℕ} [NeZero k] (σ : Fin k → Bool) :
    Function.Injective (qOf (L := L) (W := W) σ) := by
  intro p p' h
  funext i
  have := congrFun h i
  simp only [qOf, Prod.mk.injEq] at this
  exact this.2.1

/-- `|∏ E_{c_i}(p_i,p_i)| ≤ 1` for `W ≥ 1`. -/
theorem norm_loopW_le (hW : 1 ≤ W) {k : ℕ} (c : Fin k → Z2 L) (p : Fin k → Idx L W) :
    ‖loopW c p‖ ≤ 1 := by
  unfold loopW
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [Eblk_apply]
  have hW1 : ((W : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have h0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    have h1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
    nlinarith
  split_ifs
  · simpa [norm_pow] using hW1
  · simp
  · simp

/-- The coefficients of the loop form are `≤ 1`. -/
theorem coef_loopF_le {k : ℕ} [NeZero k] (hW : 1 ≤ W) (σ : Fin k → Bool) (c : Fin k → Z2 L)
    (j : Fin (k + 1)) (q : Fin j → Mono L W) : ‖(loopF σ).coef c j q‖ ≤ 1 := by
  unfold loopF homF
  simp only
  split_ifs with h
  · set q' : Fin k → Mono L W := fun i => q (Fin.cast h.symm i) with hq'
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p : Fin k → Idx L W, ‖(if q' = qOf σ p then loopW c p else 0)‖
        ≤ ∑ p : Fin k → Idx L W, (if q' = qOf σ p then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun p _ => by
            split_ifs
            · exact norm_loopW_le hW c p
            · simp
      _ ≤ 1 := by
          rw [Finset.sum_boole]
          norm_cast
          refine Finset.card_le_one.mpr fun a ha b hb => qOf_injective σ ?_
          exact (Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2
  · simp

/-- The coefficients of a constant form are its values. -/
theorem coef_constF_le {k K : ℕ} (v : (Fin k → Z2 L) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ b, ‖v b‖ ≤ B) (b : Fin k → Z2 L) (j : Fin (K + 1)) (q : Fin j → Mono L W) :
    ‖(constF v : LocalForm L W k K).coef b j q‖ ≤ B := by
  unfold constF homF
  simp only
  split_ifs
  · exact hv b
  · simpa using hB

/-- The coefficients of `lkF` are `≤ 1 + B` if `|𝒦| ≤ B`. -/
theorem coef_lkF_le {k : ℕ} [NeZero k] (hW : 1 ≤ W) (σ : Fin k → Bool) (E u : ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hK : ∀ b : Fin k → Z2 L, ‖KLoop.Kcal L W E u (loopOf σ b)‖ ≤ B)
    (c : Fin k → Z2 L) (j : Fin (k + 1)) (q : Fin j → Mono L W) :
    ‖(lkF σ E u : LocalForm L W k k).coef c j q‖ ≤ 1 + B := by
  unfold lkF addF smulF
  simp only
  refine (norm_add_le _ _).trans (add_le_add (coef_loopF_le hW σ c j q) ?_)
  rw [norm_mul, norm_neg, norm_one, one_mul]
  exact coef_constF_le _ hB hK c j q

/-- **The truncated loop form is local around the first label**, with radius `2ρ`
(the entry `(p_{i-1}, p_i)` sits in the blocks `(c_{i-1}, c_i)`, both within `maxDist c < ρ` of `c_0`). -/
theorem loc0_trunc_lkF {k : ℕ} [NeZero k] (σ : Fin k → Bool) (E u ρ : ℝ) :
    Loc0 (2 * ρ) (truncF ρ (lkF σ E u : LocalForm L W k k)) := by
  intro b j q hq i
  simp only [truncF] at hq
  by_cases hb : (KLoop.maxDist L b : ℝ) < ρ
  · simp only [hb, ↓reduceIte] at hq
    have hj0 : j.val ≠ 0 := fun h0 => absurd i.isLt (by omega)
    have hj0' : j ≠ 0 := fun h => hj0 (by rw [h]; rfl)
    have hjk : j.val = k := by
      by_contra hjk
      apply hq
      simp [lkF, addF, smulF, loopF, constF, homF, hjk, hj0']
    have hloop : (loopF (L := L) (W := W) σ).coef b j q ≠ 0 := by
      intro h0
      apply hq
      simp [lkF, addF, smulF, constF, homF, hj0', h0]
    unfold loopF homF at hloop
    simp only at hloop
    split_ifs at hloop
    obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hloop
    have hqp : (fun i : Fin k => q (Fin.cast hjk.symm i)) = qOf σ p := by
      by_contra hne
      exact hp (by simp [hne])
    have hp' : loopW b p ≠ 0 := by
      intro h0
      exact hp (by simp [h0])
    have hblock : ∀ i' : Fin k, (splitEquiv L W (p i')).1 = b i' := by
      intro i'
      unfold loopW at hp'
      have := (Finset.prod_ne_zero_iff.mp hp') i' (Finset.mem_univ _)
      rw [Eblk_apply] at this
      by_contra hne
      apply this
      simp [hne]
    set i' : Fin k := Fin.cast hjk i with hi'
    have hqi : q i = qOf σ p i' := by
      have := congrFun hqp i'
      simpa [hi'] using this
    have e1 : (splitEquiv L W (q i).1).1 = b (prvK k i') := by
      rw [hqi]; exact hblock _
    have e2 : (splitEquiv L W (q i).2.1).1 = b i' := by
      rw [hqi]; exact hblock _
    rw [e1, e2]
    have m1 := zdist2_le_maxDist b (prvK k i') 0
    have m2 := zdist2_le_maxDist b i' 0
    have m1' : (zdist2 L (b (prvK k i') - b 0) : ℝ) ≤ (KLoop.maxDist L b : ℝ) := by exact_mod_cast m1
    have m2' : (zdist2 L (b i' - b 0) : ℝ) ≤ (KLoop.maxDist L b : ℝ) := by exact_mod_cast m2
    push_cast
    linarith
  · simp only [hb, ↓reduceIte] at hq
    exact absurd rfl hq

end LoopExpansion

section ThetaBounds

variable {L : ℕ} [NeZero L]

open scoped Matrix.Norms.Operator in
/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm. -/
theorem sum_norm_row_le_opNorm (M : Matrix (Z2 L) (Z2 L) ℂ) (x : Z2 L) :
    ∑ c : Z2 L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Z2 L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Z2 L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Z2 L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- `‖(u:ℂ)‖ < 1` for `0 ≤ u < 1`. -/
theorem norm_ofReal_lt_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : ‖(u : ℂ)‖ < 1 := by
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]

open scoped Matrix.Norms.Operator in
/-- `Σ_y |Θ_u(x,y)| ≤ (1-u)⁻¹`. -/
theorem sum_norm_theta_row_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x : Z2 L) :
    ∑ y : Z2 L, ‖Theta L (u : ℂ) x y‖ ≤ (1 - u)⁻¹ := by
  refine (sum_norm_row_le_opNorm _ x).trans ?_
  have := norm_Theta_le L hL (norm_ofReal_lt_one hu0 hu1)
  rwa [Complex.norm_real, Real.norm_of_nonneg hu0] at this

/-- `(1-u)|Θ_u(x,y)| ≤ 1`. -/
theorem one_sub_mul_norm_theta_le_one (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (x y : Z2 L) : (1 - u) * ‖Theta L (u : ℂ) x y‖ ≤ 1 := by
  have h1u : 0 < 1 - u := by linarith
  have h1 : ‖Theta L (u : ℂ) x y‖ ≤ (1 - u)⁻¹ :=
    (Finset.single_le_sum (f := fun y => ‖Theta L (u : ℂ) x y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ y)).trans (sum_norm_theta_row_le hL hu0 hu1 x)
  calc (1 - u) * ‖Theta L (u : ℂ) x y‖ ≤ (1 - u) * (1 - u)⁻¹ := mul_le_mul_of_nonneg_left h1 h1u.le
    _ = 1 := mul_inv_cancel₀ h1u.ne'

/-- The generator at `ξ = 1` is `S Θ_u`. -/
theorem thetaGenMat_one_eq (u : ℝ) : thetaGenMat L 1 u = SB L * Theta L (u : ℂ) := by
  simp [thetaGenMat]

open scoped Matrix.Norms.Operator in
/-- The row `ℓ¹` bound of the generator at `ξ = 1`: `Σ_c |(S Θ_u)(x,c)| ≤ (1-u)⁻¹`. -/
theorem sum_norm_T_row_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x : Z2 L) :
    ∑ c : Z2 L, ‖thetaGenMat L 1 u x c‖ ≤ (1 - u)⁻¹ := by
  rw [thetaGenMat_one_eq]
  refine (sum_norm_row_le_opNorm _ x).trans ?_
  calc ‖SB L * Theta L (u : ℂ)‖ ≤ ‖SB L‖ * ‖Theta L (u : ℂ)‖ := norm_mul_le _ _
    _ = ‖Theta L (u : ℂ)‖ := by rw [norm_SB L hL, one_mul]
    _ ≤ (1 - ‖(u : ℂ)‖)⁻¹ := norm_Theta_le L hL (norm_ofReal_lt_one hu0 hu1)
    _ = (1 - u)⁻¹ := by rw [Complex.norm_real, Real.norm_of_nonneg hu0]

/-- The kernel `S Θ_ζ` is symmetric. -/
theorem SB_mul_Theta_symm (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (x y : Z2 L) :
    (SB L * Theta L ζ) x y = (SB L * Theta L ζ) y x := by
  have h : (SB L * Theta L ζ)ᵀ = SB L * Theta L ζ := by
    rw [Matrix.transpose_mul, SB_transpose, Theta_transpose L hL hζ]
    exact (Theta_commute_SB L hL hζ).eq
  have := congrFun (congrFun h y) x
  simpa [Matrix.transpose_apply] using this

/-- The column sums of `S Θ_ζ` are the constant `(1 - ζ)⁻¹`. -/
theorem col_sum_SB_mul_Theta (hL : 3 ≤ L) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (y : Z2 L) :
    ∑ c : Z2 L, (SB L * Theta L ζ) c y = (1 - ζ)⁻¹ := by
  simp_rw [SB_mul_Theta_symm hL hζ _ y]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_Theta_row L hL hζ]
  rw [← Finset.sum_mul, sum_SB_row L hL y, one_mul]

/-- The column sums of the generator at `ξ = 1` are the constant `(1-u)⁻¹`. -/
theorem col_sum_T (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (y : Z2 L) :
    ∑ c : Z2 L, thetaGenMat L 1 u c y = (((1 - u)⁻¹ : ℝ) : ℂ) := by
  rw [thetaGenMat_one_eq]
  rw [col_sum_SB_mul_Theta hL (norm_ofReal_lt_one hu0 hu1) y]
  push_cast
  rfl

/-- The entries of `S Θ_u` are `≤ (1-u)⁻¹`. -/
theorem norm_T_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x y : Z2 L) :
    ‖thetaGenMat L 1 u x y‖ ≤ (1 - u)⁻¹ :=
  (Finset.single_le_sum (f := fun y => ‖thetaGenMat L 1 u x y‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ y)).trans (sum_norm_T_row_le hL hu0 hu1 x)

/-! ### Property 5 in the slot form, decay of `S Θ_u` and of `ϑ_u` -/

/-- The constant `C₅ = 180·40002²` of `norm_Theta_apply_le_prop5`. -/
def C5 : ℝ := 180 * 40002 ^ 2

/-- `C₅ > 0`. -/
theorem C5_pos : 0 < C5 := by unfold C5; positivity

/-- The slot constant `c_L(u) = C₅(1+log L)ℓ_u^{-2}`. -/
def cL (L : ℕ) (u : ℝ) : ℝ := C5 * (1 + Real.log L) * (ellT L u ^ 2)⁻¹

/-- `c_L(u) ≥ 0`. -/
theorem cL_nonneg (L : ℕ) (u : ℝ) : 0 ≤ cL L u := by
  have hlog : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  unfold cL
  exact mul_nonneg (mul_nonneg C5_pos.le hlog) (inv_nonneg.mpr (sq_nonneg _))

/-- The decay factor `exp(-r/(20000 ℓ_u))` of property 5. -/
def dec (L : ℕ) (u r : ℝ) : ℝ := Real.exp (-r / (20000 * ellT L u))

/-- `dec > 0`. -/
theorem dec_pos (L : ℕ) (u r : ℝ) : 0 < dec L u r := Real.exp_pos _

/-- `dec(r + s) = dec(r) dec(s)`. -/
theorem dec_add (L : ℕ) (u r s : ℝ) : dec L u (r + s) = dec L u r * dec L u s := by
  unfold dec
  rw [← Real.exp_add]
  congr 1
  ring

/-- `dec` is decreasing. -/
theorem dec_anti (L : ℕ) {u : ℝ} (hℓ : 0 < ellT L u) {r s : ℝ} (h : r ≤ s) : dec L u s ≤ dec L u r := by
  unfold dec
  refine Real.exp_le_exp.mpr ?_
  exact div_le_div_of_nonneg_right (neg_le_neg h) (by positivity)

/-- Property 5 at `ξ = u ∈ [0,1)` (`κ(u)² = 1 - u`, `ℓ̂(u) = ℓ_u`):
`(1-u)|Θ_u(x,y)| ≤ c_L(u) exp(-|x-y|_L/(20000ℓ_u))`. -/
theorem theta_decay (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x y : Z2 L) :
    (1 - u) * ‖Theta L (u : ℂ) x y‖ ≤ cL L u * dec L u (zdist2 L (x - y) : ℝ) := by
  have hξ : ‖(u : ℂ)‖ < 1 := norm_ofReal_lt_one hu0 hu1
  have h5 := norm_Theta_apply_le_prop5 L hL (u : ℂ) hξ x y
  have hell : ellhat L (u : ℂ) = ellT L u := kloop_ellT_eq hu1.le
  have hkap : kappa (u : ℂ) ^ 2 = 1 - u := by
    rw [kappa_sq]
    have h : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; rfl
    rw [h, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hell, hkap] at h5
  have h1u : 0 < 1 - u := by linarith
  calc (1 - u) * ‖Theta L (u : ℂ) x y‖
      ≤ (1 - u) * (180 * 40002 ^ 2 * (1 + Real.log L) * ((1 - u) * ellT L u ^ 2)⁻¹ *
          Real.exp (-(zdist2 L (x - y) : ℝ) / (20000 * ellT L u))) :=
        mul_le_mul_of_nonneg_left h5 h1u.le
    _ = cL L u * dec L u (zdist2 L (x - y) : ℝ) := by
        unfold cL dec C5
        rw [mul_inv]
        field_simp

/-- The rows of `S^{(B)}` have `ℓ¹` norm `1`. -/
theorem sum_norm_SB_row_real (hL : 3 ≤ L) (x : Z2 L) : ∑ z : Z2 L, ‖SB L x z‖ = 1 := by
  have h := sum_nnnorm_SB_row L hL x
  have h' : ((∑ z : Z2 L, ‖SB L x z‖₊ : NNReal) : ℝ) = 1 := by rw [h]; rfl
  simpa using h'

/-- `exp(1/(20000 ℓ_u)) ≤ 3` (`ℓ_u ≥ 1`). -/
theorem exp_inv_le_three (hL : 1 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.exp (1 / (20000 * ellT L u)) ≤ 3 := by
  have h1 : 1 ≤ ellT L u := one_le_ellT hL hu0 hu1
  have h2 : 1 / (20000 * ellT L u) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  calc Real.exp (1 / (20000 * ellT L u)) ≤ Real.exp 1 := Real.exp_le_exp.mpr h2
    _ ≤ 3 := Real.exp_one_lt_three.le

/-- The decay of the generator `S Θ_u` (range one of `S`): `(1-u)|(SΘ_u)(x,y)| ≤ 3 c_L(u) exp(-|x-y|/(20000ℓ_u))`. -/
theorem T_decay (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x y : Z2 L) :
    (1 - u) * ‖thetaGenMat L 1 u x y‖ ≤ 3 * cL L u * dec L u (zdist2 L (x - y) : ℝ) := by
  have hL1 : 1 ≤ L := by omega
  have h1u : 0 < 1 - u := by linarith
  have hc0 := cL_nonneg L u
  have hℓ : 0 < ellT L u := (ellT_pos_le hL1 hu1).1
  rw [thetaGenMat_one_eq, Matrix.mul_apply]
  have hterm : ∀ z : Z2 L, (1 - u) * ‖SB L x z * Theta L (u : ℂ) z y‖ ≤
      ‖SB L x z‖ * (3 * cL L u * dec L u (zdist2 L (x - y) : ℝ)) := by
    intro z
    by_cases hz : SB L x z = 0
    · simp [hz]
    · have hzd : zdist2 L (x - z) ≤ 1 := by
        by_contra h
        exact hz (SB_apply_eq_zero L hL (by omega))
      have htri := zdist2_sub_le L x z y
      have hd : (zdist2 L (x - y) : ℝ) - 1 ≤ (zdist2 L (z - y) : ℝ) := by
        have : zdist2 L (x - y) ≤ 1 + zdist2 L (z - y) := by omega
        have h' : (zdist2 L (x - y) : ℝ) ≤ 1 + (zdist2 L (z - y) : ℝ) := by exact_mod_cast this
        linarith
      have hdec := theta_decay hL hu0 hu1 z y
      have hdec2 : dec L u (zdist2 L (z - y) : ℝ) ≤ 3 * dec L u (zdist2 L (x - y) : ℝ) := by
        calc dec L u (zdist2 L (z - y) : ℝ) ≤ dec L u ((zdist2 L (x - y) : ℝ) - 1) :=
              dec_anti L hℓ hd
          _ = Real.exp (1 / (20000 * ellT L u)) * dec L u (zdist2 L (x - y) : ℝ) := by
              unfold dec
              rw [← Real.exp_add]
              congr 1
              field_simp
              ring
          _ ≤ 3 * dec L u (zdist2 L (x - y) : ℝ) :=
              mul_le_mul_of_nonneg_right (exp_inv_le_three hL1 hu0 hu1) (dec_pos L u _).le
      rw [norm_mul]
      calc (1 - u) * (‖SB L x z‖ * ‖Theta L (u : ℂ) z y‖)
          = ‖SB L x z‖ * ((1 - u) * ‖Theta L (u : ℂ) z y‖) := by ring
        _ ≤ ‖SB L x z‖ * (cL L u * dec L u (zdist2 L (z - y) : ℝ)) :=
            mul_le_mul_of_nonneg_left hdec (norm_nonneg _)
        _ ≤ ‖SB L x z‖ * (cL L u * (3 * dec L u (zdist2 L (x - y) : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdec2 hc0) (norm_nonneg _)
        _ = ‖SB L x z‖ * (3 * cL L u * dec L u (zdist2 L (x - y) : ℝ)) := by ring
  calc (1 - u) * ‖∑ z : Z2 L, SB L x z * Theta L (u : ℂ) z y‖
      ≤ (1 - u) * ∑ z : Z2 L, ‖SB L x z * Theta L (u : ℂ) z y‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) h1u.le
    _ = ∑ z : Z2 L, (1 - u) * ‖SB L x z * Theta L (u : ℂ) z y‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ z : Z2 L, ‖SB L x z‖ * (3 * cL L u * dec L u (zdist2 L (x - y) : ℝ)) :=
        Finset.sum_le_sum fun z _ => hterm z
    _ = 3 * cL L u * dec L u (zdist2 L (x - y) : ℝ) := by
        rw [← Finset.sum_mul, sum_norm_SB_row_real hL x, one_mul]

end ThetaBounds

section Vartheta

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `‖ϑ_{u,a}‖ = Π_{i ≠ 0} (1-u)‖Θ_u(a₀,a_i)‖`. -/
theorem norm_vartheta_eq {u : ℝ} (hu1 : u < 1) (a : Fin k → Z2 L) :
    ‖vartheta L u a‖ = ∏ i ∈ Finset.univ.erase (0 : Fin k),
      ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖) := by
  unfold vartheta
  rw [norm_mul, norm_pow, norm_prod, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]

/-- **`|ϑ_{u,a}| ≤ 1`.** -/
theorem norm_vartheta_le_one (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Fin k → Z2 L) :
    ‖vartheta L u a‖ ≤ 1 := by
  rw [norm_vartheta_eq hu1]
  refine Finset.prod_le_one₀ (fun i _ => mul_nonneg (by linarith) (norm_nonneg _)) (fun i _ => ?_)
  exact one_sub_mul_norm_theta_le_one hL hu0 hu1 _ _

/-- The slot bound: `|ϑ_{u,a}| ≤ (1-u)|Θ_u(a₀, a_m)|` for every slot `m ≠ 0`. -/
theorem norm_vartheta_le_slot (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Fin k → Z2 L)
    {m : Fin k} (hm : m ≠ 0) : ‖vartheta L u a‖ ≤ (1 - u) * ‖Theta L (u : ℂ) (a 0) (a m)‖ := by
  rw [norm_vartheta_eq hu1]
  have hmS : m ∈ Finset.univ.erase (0 : Fin k) := Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ (fun i => (1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖) hmS]
  have h1 : ∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase m,
      ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => mul_nonneg (by linarith) (norm_nonneg _))
      (fun i _ => one_sub_mul_norm_theta_le_one hL hu0 hu1 _ _)
  have h0 : 0 ≤ (1 - u) * ‖Theta L (u : ℂ) (a 0) (a m)‖ :=
    mul_nonneg (by linarith) (norm_nonneg _)
  calc _ ≤ ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a m)‖) * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = _ := mul_one _

/-- The slot bound with the decay of property 5. -/
theorem norm_vartheta_le_decay (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (a : Fin k → Z2 L) {m : Fin k} (hm : m ≠ 0) {r : ℝ} (hr : r ≤ (zdist2 L (a 0 - a m) : ℝ)) :
    ‖vartheta L u a‖ ≤ cL L u * dec L u r := by
  have hℓ : 0 < ellT L u := (ellT_pos_le (by omega) hu1).1
  refine (norm_vartheta_le_slot hL hu0 hu1 a hm).trans ((theta_decay hL hu0 hu1 _ _).trans ?_)
  exact mul_le_mul_of_nonneg_left (dec_anti L hℓ hr) (cL_nonneg L u)

end Vartheta

section ThetaSig

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `m m̄ = |m|² = 1` for `|E| ≤ 2`. -/
theorem mSig_mul_conj {E : ℝ} (hE : |E| ≤ 2) :
    KLoop.mSig E true * KLoop.mSig E false = 1 := by
  simp only [KLoop.mSig, ↓reduceIte, Bool.false_eq_true]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Gauss.norm_spectralM hE]
  simp

/-- For alternating `σ` every edge factor `ξ_i = m(σ_i) m(σ_{i+1}) = m m̄ = 1`. -/
theorem xi_one {E : ℝ} (hE : |E| ≤ 2) {σ : Fin k → Bool} (hσ : Alternating σ) (i : Fin k) :
    KLoop.mSig E (σ i) * KLoop.mSig E (σ (i + 1)) = 1 := by
  rw [hσ i]
  cases h : σ i
  · simp only [Bool.not_false]
    rw [mul_comm]; exact mSig_mul_conj hE
  · simp only [Bool.not_true]
    exact mSig_mul_conj hE

/-- **`ϴ_{u,σ}` for alternating `σ`**: every kernel is the diffusive `S Θ_u` (`ξ_i = 1`). -/
theorem thetaSig_alt {E : ℝ} (hE : |E| ≤ 2) {σ : Fin k → Bool} (hσ : Alternating σ) (u : ℝ)
    (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    thetaSig L E σ u A a =
      ∑ i : Fin k, ∑ b : Z2 L, thetaGenMat L 1 u (a i) b * A (Function.update a i b) := by
  unfold thetaSig
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  rw [xi_one hE hσ i]

end ThetaSig

section PsumTheta

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- The involution `(a, b) ↦ (a[i := b], a_i)` of `(Z_L²)^k × Z_L²`. -/
def swapEq (i : Fin k) : ((Fin k → Z2 L) × Z2 L) ≃ ((Fin k → Z2 L) × Z2 L) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · simp [Function.update_idem, Function.update_eq_self]
    · simp
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · simp [Function.update_idem, Function.update_eq_self]
    · simp

/-- The change of variables `(a, b) ↦ (a[i := b], a_i)` in a double sum. -/
theorem sum_swap (i : Fin k) (F : (Fin k → Z2 L) → Z2 L → ℂ) :
    ∑ a, ∑ b, F a b = ∑ a, ∑ y, F (Function.update a i y) (a i) := by
  rw [← Fintype.sum_prod_type' (f := F),
    ← Fintype.sum_prod_type' (f := fun a y => F (Function.update a i y) (a i))]
  exact ((swapEq i).sum_comp (fun p => F p.1 p.2)).symm

/-- `Σ_a f(a₀) 𝒜_a = Σ_b f(b) (𝒫𝒜)_b`. -/
theorem sum_first (f : Z2 L → ℂ) (A : (Fin k → Z2 L) → ℂ) :
    ∑ a, f (a 0) * A a = ∑ b, f b * Psum L A b := by
  unfold Psum
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- `𝒫` as a sum with an indicator. -/
theorem psum_eq_sum (A : (Fin k → Z2 L) → ℂ) (a₀ : Z2 L) :
    Psum L A a₀ = ∑ a, if a 0 = a₀ then A a else 0 := by
  unfold Psum
  rw [Finset.sum_filter]

/-- **`𝒫ϴ = ϴ₀𝒫 + const 𝒫`** for alternating `σ`: `Σ_{a : a_0 = a₀} (ϴ𝒜)_a = Σ_b T(a₀,b) (𝒫𝒜)_b +
(k-1)(1-u)⁻¹ (𝒫𝒜)_{a₀}` (slot `0` moves the label that `𝒫` fixes; every other slot moves a summed
label, and the column sums of `T = SΘ_u` are `(1-u)⁻¹`). -/
theorem psum_thetaSig_alt (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {E : ℝ} (hE : |E| ≤ 2)
    {σ : Fin k → Bool} (hσ : Alternating σ) (A : (Fin k → Z2 L) → ℂ) (a₀ : Z2 L) :
    Psum L (thetaSig L E σ u A) a₀ =
      ∑ b, thetaGenMat L 1 u a₀ b * Psum L A b +
        ((k - 1 : ℕ) : ℂ) * (((1 - u)⁻¹ : ℝ) : ℂ) * Psum L A a₀ := by
  rw [psum_eq_sum]
  simp only [thetaSig_alt hE hσ]
  have h1 : ∀ a : Fin k → Z2 L,
      (if a 0 = a₀ then ∑ i : Fin k, ∑ b : Z2 L, thetaGenMat L 1 u (a i) b *
        A (Function.update a i b) else 0) =
      ∑ i : Fin k, ∑ b : Z2 L, (if a 0 = a₀ then thetaGenMat L 1 u (a i) b *
        A (Function.update a i b) else 0) := by
    intro a
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  have hi : ∀ i : Fin k, ∑ a : Fin k → Z2 L, ∑ b : Z2 L, (if a 0 = a₀ then
      thetaGenMat L 1 u (a i) b * A (Function.update a i b) else 0) =
      ∑ a : Fin k → Z2 L, ∑ y : Z2 L, (if (Function.update a i y) 0 = a₀ then
        thetaGenMat L 1 u y (a i) * A a else 0) := by
    intro i
    rw [sum_swap i (fun a b => if a 0 = a₀ then thetaGenMat L 1 u (a i) b *
      A (Function.update a i b) else 0)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
    simp [Function.update_self, Function.update_idem, Function.update_eq_self]
  simp_rw [hi]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin k))]
  congr 1
  · -- slot 0
    simp only [Function.update_self]
    have : ∀ a : Fin k → Z2 L, (∑ y : Z2 L, if y = a₀ then thetaGenMat L 1 u y (a 0) * A a else 0) =
        thetaGenMat L 1 u a₀ (a 0) * A a := by
      intro a
      rw [Finset.sum_ite_eq' Finset.univ a₀ (fun y => thetaGenMat L 1 u y (a 0) * A a)]
      simp
    simp_rw [this]
    rw [sum_first (fun b => thetaGenMat L 1 u a₀ b) A]
  · -- slots `i ≠ 0`
    have hslot : ∀ i ∈ Finset.univ.erase (0 : Fin k),
        ∑ a : Fin k → Z2 L, ∑ y : Z2 L, (if (Function.update a i y) 0 = a₀ then
          thetaGenMat L 1 u y (a i) * A a else 0) =
        (((1 - u)⁻¹ : ℝ) : ℂ) * Psum L A a₀ := by
      intro i hi
      have hne : (0 : Fin k) ≠ i := fun h => (Finset.mem_erase.mp hi).1 h.symm
      simp only [Function.update_of_ne hne]
      have : ∀ a : Fin k → Z2 L, (∑ y : Z2 L, if a 0 = a₀ then thetaGenMat L 1 u y (a i) * A a else 0) =
          if a 0 = a₀ then (((1 - u)⁻¹ : ℝ) : ℂ) * A a else 0 := by
        intro a
        split_ifs
        · rw [← Finset.sum_mul, col_sum_T hL hu0 hu1]
        · simp
      simp_rw [this]
      rw [psum_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hslot, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

end PsumTheta

section KernelB4

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- `Φ₀(a, x) = T(a₀,x)(ϑ(a[0 := x]) - ϑ(a))`, `T = S Θ_u`. -/
def phi0 (u : ℝ) (a : Fin k → Z2 L) (x : Z2 L) : ℂ :=
  thetaGenMat L 1 u (a 0) x * (vartheta L u (Function.update a 0 x) - vartheta L u a)

/-- `Φ₁(a) = Σ_{i ≠ 0} (Σ_b T(a_i,b) ϑ(a[i := b]) - (1-u)⁻¹ ϑ(a))`. -/
def phi1 (u : ℝ) (a : Fin k → Z2 L) : ℂ :=
  ∑ i ∈ Finset.univ.erase (0 : Fin k),
    (∑ b, thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b) -
      (((1 - u)⁻¹ : ℝ) : ℂ) * vartheta L u a)

/-- **The kernel of `ℬ₄ = [𝒬_u, ϴ_{u,σ}]` for alternating `σ`**: `ℬ₄(𝒜)_a = Σ_c 𝔎_{a,c} 𝒜_c` with
`𝔎_{a,c} = Φ₀(a, c₀) + 1(c₀ = a₀) Φ₁(a)` (it depends on `c` only through `c₀`, because `ℬ₄` sees `𝒜`
only through `𝒫𝒜`). -/
def kerB4 (u : ℝ) (a c : Fin k → Z2 L) : ℂ :=
  phi0 u a (c 0) + (if c 0 = a 0 then phi1 u a else 0)

/-- **The commutator `[𝒬_u, ϴ_{u,σ}]` as a kernel** (`eq:case4_B`). -/
theorem commutator_eq_kerB4 (hL : 3 ≤ L) (hk : 2 ≤ k) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {E : ℝ} (hE : |E| ≤ 2) {σ : Fin k → Bool} (hσ : Alternating σ)
    (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    Qop L u (thetaSig L E σ u A) a - thetaSig L E σ u (Qop L u A) a =
      ∑ c, kerB4 u a c * A c := by
  have h7 := (qopAlgebra L hL k hk u hu0 hu1).2.2.2.2.2.2 E σ A a
  have hA1 : thetaSig L E σ u (fun b => Psum L A (b 0) * vartheta L u b) a =
      ∑ b, thetaGenMat L 1 u (a 0) b * (Psum L A b * vartheta L u (Function.update a 0 b)) +
        ∑ i ∈ Finset.univ.erase (0 : Fin k), Psum L A (a 0) *
          ∑ b, thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b) := by
    calc thetaSig L E σ u (fun b => Psum L A (b 0) * vartheta L u b) a
        = ∑ i : Fin k, ∑ b : Z2 L, thetaGenMat L 1 u (a i) b *
            (Psum L A ((Function.update a i b) 0) * vartheta L u (Function.update a i b)) := by
          rw [thetaSig_alt hE hσ]
      _ = (∑ b : Z2 L, thetaGenMat L 1 u (a 0) b *
            (Psum L A ((Function.update a 0 b) 0) * vartheta L u (Function.update a 0 b))) +
          ∑ i ∈ Finset.univ.erase (0 : Fin k), ∑ b : Z2 L, thetaGenMat L 1 u (a i) b *
            (Psum L A ((Function.update a i b) 0) * vartheta L u (Function.update a i b)) :=
          (Finset.add_sum_erase _ (fun i => ∑ b : Z2 L, thetaGenMat L 1 u (a i) b *
            (Psum L A ((Function.update a i b) 0) * vartheta L u (Function.update a i b)))
            (Finset.mem_univ (0 : Fin k))).symm
      _ = ∑ b, thetaGenMat L 1 u (a 0) b * (Psum L A b * vartheta L u (Function.update a 0 b)) +
        ∑ i ∈ Finset.univ.erase (0 : Fin k), Psum L A (a 0) *
          ∑ b, thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b) := by
          refine congrArg₂ (· + ·) ?_ ?_
          · refine Finset.sum_congr rfl fun b _ => ?_
            simp [Function.update_self]
          · refine Finset.sum_congr rfl fun i hi => ?_
            have hne : (0 : Fin k) ≠ i := fun h => (Finset.mem_erase.mp hi).1 h.symm
            simp only [Function.update_of_ne hne]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
  have hK : ∑ c, kerB4 u a c * A c =
      ∑ b, phi0 u a b * Psum L A b + phi1 u a * Psum L A (a 0) := by
    unfold kerB4
    simp_rw [add_mul, Finset.sum_add_distrib]
    congr 1
    · exact sum_first (fun b => phi0 u a b) A
    · rw [psum_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> simp
  rw [h7, hA1, psum_thetaSig_alt hL hu0 hu1 hE hσ A (a 0), hK]
  unfold phi0 phi1
  have e1 : ∑ b, thetaGenMat L 1 u (a 0) b * (vartheta L u (Function.update a 0 b) - vartheta L u a) *
        Psum L A b =
      ∑ b, thetaGenMat L 1 u (a 0) b * (Psum L A b * vartheta L u (Function.update a 0 b)) -
        (∑ b, thetaGenMat L 1 u (a 0) b * Psum L A b) * vartheta L u a := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e2 : (∑ i ∈ Finset.univ.erase (0 : Fin k),
        (∑ b, thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b) -
          (((1 - u)⁻¹ : ℝ) : ℂ) * vartheta L u a)) * Psum L A (a 0) =
      ∑ i ∈ Finset.univ.erase (0 : Fin k), Psum L A (a 0) *
          ∑ b, thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b) -
        ((k - 1 : ℕ) : ℂ) * (((1 - u)⁻¹ : ℝ) : ℂ) * Psum L A (a 0) * vartheta L u a := by
    rw [Finset.sum_sub_distrib, sub_mul, Finset.sum_mul, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · ring
  rw [e1, e2]
  ring

/-! ### Bounds on the kernel `𝔎` -/

/-- A pair of slots at distance `≥ R` forces a slot `m ≠ 0` at distance `≥ R/2` from `a₀`. -/
theorem exists_far {R : ℝ} (hR : 0 < R) {a : Fin k → Z2 L}
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
    rw [e, zdist2_neg'] at h1
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

/-- **`K1`**: `|Φ₀(a,x)| ≤ 2(1-u)⁻¹`. -/
theorem norm_phi0_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Fin k → Z2 L)
    (x : Z2 L) : ‖phi0 u a x‖ ≤ 2 * (1 - u)⁻¹ := by
  unfold phi0
  rw [norm_mul]
  have h1 := norm_T_le hL hu0 hu1 (a 0) x
  have h2 : ‖vartheta L u (Function.update a 0 x) - vartheta L u a‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have := norm_vartheta_le_one hL hu0 hu1 (Function.update a 0 x)
    have := norm_vartheta_le_one hL hu0 hu1 a
    linarith
  calc ‖thetaGenMat L 1 u (a 0) x‖ * ‖vartheta L u (Function.update a 0 x) - vartheta L u a‖
      ≤ (1 - u)⁻¹ * 2 := mul_le_mul h1 h2 (norm_nonneg _) (inv_nonneg.2 (by linarith))
    _ = 2 * (1 - u)⁻¹ := by ring

/-- **`K1`**: `|Φ₁(a)| ≤ 2(k-1)(1-u)⁻¹`. -/
theorem norm_phi1_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Fin k → Z2 L) :
    ‖phi1 u a‖ ≤ 2 * ((k : ℝ) - 1) * (1 - u)⁻¹ := by
  unfold phi1
  have h1u : 0 < 1 - u := by linarith
  have hterm : ∀ i ∈ Finset.univ.erase (0 : Fin k),
      ‖∑ b, thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b) -
        (((1 - u)⁻¹ : ℝ) : ℂ) * vartheta L u a‖ ≤ 2 * (1 - u)⁻¹ := by
    intro i _
    refine (norm_sub_le _ _).trans ?_
    have hA : ‖∑ b, thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b)‖ ≤
        (1 - u)⁻¹ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ b, ‖thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b)‖
          ≤ ∑ b, ‖thetaGenMat L 1 u (a i) b‖ := Finset.sum_le_sum fun b _ => by
            rw [norm_mul]
            exact mul_le_of_le_one_right (norm_nonneg _)
              (norm_vartheta_le_one hL hu0 hu1 _)
        _ ≤ (1 - u)⁻¹ := sum_norm_T_row_le hL hu0 hu1 (a i)
    have hB : ‖(((1 - u)⁻¹ : ℝ) : ℂ) * vartheta L u a‖ ≤ (1 - u)⁻¹ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 h1u.le)]
      exact mul_le_of_le_one_right (inv_nonneg.2 h1u.le) (norm_vartheta_le_one hL hu0 hu1 a)
    linarith
  calc ‖∑ i ∈ Finset.univ.erase (0 : Fin k), _‖
      ≤ ∑ i ∈ Finset.univ.erase (0 : Fin k), 2 * (1 - u)⁻¹ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = 2 * ((k : ℝ) - 1) * (1 - u)⁻¹ := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (NeZero.pos k)]; simp
        rw [this]; ring

/-- **`K1`**: `|𝔎_{a,c}| ≤ 2k(1-u)⁻¹`. -/
theorem norm_kerB4_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a c : Fin k → Z2 L) :
    ‖kerB4 u a c‖ ≤ 2 * (k : ℝ) * (1 - u)⁻¹ := by
  unfold kerB4
  refine (norm_add_le _ _).trans ?_
  have h0 := norm_phi0_le hL hu0 hu1 a (c 0)
  have h1 := norm_phi1_le hL hu0 hu1 a
  have h1u : 0 < 1 - u := by linarith
  have h2 : ‖(if c 0 = a 0 then phi1 u a else 0)‖ ≤ 2 * ((k : ℝ) - 1) * (1 - u)⁻¹ := by
    split_ifs
    · exact h1
    · have : (0 : ℝ) ≤ (k : ℝ) - 1 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast NeZero.pos k
        linarith
      simpa using mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) this) (inv_nonneg.2 h1u.le)
  nlinarith

/-- `‖T(x,y)‖ ≤ (1-u)⁻¹ · 3 c_L dec(|x-y|)`. -/
theorem norm_T_le_decay (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x y : Z2 L) :
    ‖thetaGenMat L 1 u x y‖ ≤ (1 - u)⁻¹ * (3 * cL L u * dec L u (zdist2 L (x - y) : ℝ)) := by
  have h1u : 0 < 1 - u := by linarith
  have h := T_decay hL hu0 hu1 x y
  calc ‖thetaGenMat L 1 u x y‖ = (1 - u)⁻¹ * ((1 - u) * ‖thetaGenMat L 1 u x y‖) := by
        field_simp
    _ ≤ (1 - u)⁻¹ * (3 * cL L u * dec L u (zdist2 L (x - y) : ℝ)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 h1u.le)

/-- **`K2`** (decay in the first label): if `|c₀ - a₀| ≥ r > 0` then
`|𝔎_{a,c}| ≤ 2 (1-u)⁻¹ · 3 c_L dec(r)` (the kernel is `Φ₀(a, c₀) = T(a₀,c₀)(ϑ - ϑ)`). -/
theorem norm_kerB4_le_near (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a c : Fin k → Z2 L)
    {r : ℝ} (hr : 0 < r) (hnear : r ≤ (zdist2 L (c 0 - a 0) : ℝ)) :
    ‖kerB4 u a c‖ ≤ 2 * ((1 - u)⁻¹ * (3 * cL L u * dec L u r)) := by
  have hne : c 0 ≠ a 0 := by
    intro h
    rw [h, sub_self, zdist2_zero] at hnear
    simp at hnear
    linarith
  have hℓ : 0 < ellT L u := (ellT_pos_le (by omega) hu1).1
  unfold kerB4
  simp only [hne, ↓reduceIte, add_zero]
  unfold phi0
  rw [norm_mul]
  have h2 : ‖vartheta L u (Function.update a 0 (c 0)) - vartheta L u a‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have := norm_vartheta_le_one hL hu0 hu1 (Function.update a 0 (c 0))
    have := norm_vartheta_le_one hL hu0 hu1 a
    linarith
  have hT := norm_T_le_decay hL hu0 hu1 (a 0) (c 0)
  have hdd : dec L u (zdist2 L (a 0 - c 0) : ℝ) ≤ dec L u r := by
    refine dec_anti L hℓ ?_
    rw [zdist2_symm L (a 0) (c 0)]
    exact hnear
  have hT' : ‖thetaGenMat L 1 u (a 0) (c 0)‖ ≤ (1 - u)⁻¹ * (3 * cL L u * dec L u r) :=
    hT.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdd
      (mul_nonneg (by norm_num) (cL_nonneg L u))) (inv_nonneg.2 (by linarith)))
  have h0 : 0 ≤ (1 - u)⁻¹ * (3 * cL L u * dec L u r) :=
    mul_nonneg (inv_nonneg.2 (by linarith)) (mul_nonneg (mul_nonneg (by norm_num) (cL_nonneg L u))
      (dec_pos L u r).le)
  calc ‖thetaGenMat L 1 u (a 0) (c 0)‖ * ‖vartheta L u (Function.update a 0 (c 0)) - vartheta L u a‖
      ≤ ((1 - u)⁻¹ * (3 * cL L u * dec L u r)) * 2 := mul_le_mul hT' h2 (norm_nonneg _) h0
    _ = 2 * ((1 - u)⁻¹ * (3 * cL L u * dec L u r)) := by ring

/-- **`K3`, the pointwise bound**: if `|a_0 - a_{j₀}| ≥ r/2` with `j₀ ≠ 0`, every term
`T(a_i, b) ϑ(a[i := b])`, `i ≠ 0`, and `T(a_0, x) ϑ(a[0 := x])` is `≤ (1-u)⁻¹ (3c² + c) dec(r/2)`. -/
theorem norm_T_vartheta_le_far (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Fin k → Z2 L)
    {j₀ : Fin k} (hj0 : j₀ ≠ 0) {r : ℝ} (hj : r / 2 ≤ (zdist2 L (a 0 - a j₀) : ℝ)) :
    (∀ (i : Fin k) (b : Z2 L), i ≠ 0 →
      ‖thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b)‖ ≤
        (1 - u)⁻¹ * ((3 * cL L u ^ 2 + cL L u) * dec L u (r / 2))) ∧
    (∀ x : Z2 L, ‖thetaGenMat L 1 u (a 0) x * vartheta L u (Function.update a 0 x)‖ ≤
        (1 - u)⁻¹ * ((3 * cL L u ^ 2 + cL L u) * dec L u (r / 2))) := by
  have hL1 : 1 ≤ L := by omega
  have hℓ : 0 < ellT L u := (ellT_pos_le hL1 hu1).1
  have h1u : 0 < 1 - u := by linarith
  have hC := cL_nonneg L u
  have hτ : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
  have hδ := (dec_pos L u (r / 2)).le
  have hbig : 3 * cL L u ^ 2 ≤ 3 * cL L u ^ 2 + cL L u := by linarith
  have hsmall : cL L u ≤ 3 * cL L u ^ 2 + cL L u := by nlinarith [sq_nonneg (cL L u)]
  refine ⟨fun i b hi => ?_, fun x => ?_⟩
  · by_cases hij : i = j₀
    · -- `i = i`: the slot `i` carries `b`, joined to `a₀` by `Θ` and to `a_{i}` by `T`
      subst hij
      have hne0 : i ≠ 0 := hi
      have e0 : (Function.update a i b) 0 = a 0 := Function.update_of_ne (Ne.symm hne0) _ _
      have hv := norm_vartheta_le_slot hL hu0 hu1 (Function.update a i b) hne0
      rw [e0, Function.update_self] at hv
      have hv' : ‖vartheta L u (Function.update a i b)‖ ≤ cL L u * dec L u (zdist2 L (a 0 - b) : ℝ) :=
        hv.trans (theta_decay hL hu0 hu1 _ _)
      have hT := norm_T_le_decay hL hu0 hu1 (a i) b
      have htri := zdist2_sub_le L (a 0) b (a i)
      have hsum : r / 2 ≤ (zdist2 L (a i - b) : ℝ) + (zdist2 L (a 0 - b) : ℝ) := by
        have h' : (zdist2 L (a 0 - a i) : ℝ) ≤
            (zdist2 L (a 0 - b) : ℝ) + (zdist2 L (b - a i) : ℝ) := by exact_mod_cast htri
        rw [zdist2_symm L b (a i)] at h'
        linarith
      rw [norm_mul]
      calc ‖thetaGenMat L 1 u (a i) b‖ * ‖vartheta L u (Function.update a i b)‖
          ≤ ((1 - u)⁻¹ * (3 * cL L u * dec L u (zdist2 L (a i - b) : ℝ))) *
              (cL L u * dec L u (zdist2 L (a 0 - b) : ℝ)) :=
            mul_le_mul hT hv' (norm_nonneg _) (mul_nonneg hτ (mul_nonneg (mul_nonneg (by norm_num) hC)
              (dec_pos L u _).le))
        _ = (1 - u)⁻¹ * (3 * cL L u ^ 2 * (dec L u (zdist2 L (a i - b) : ℝ) *
              dec L u (zdist2 L (a 0 - b) : ℝ))) := by ring
        _ = (1 - u)⁻¹ * (3 * cL L u ^ 2 * dec L u ((zdist2 L (a i - b) : ℝ) +
              (zdist2 L (a 0 - b) : ℝ))) := by rw [dec_add]
        _ ≤ (1 - u)⁻¹ * (3 * cL L u ^ 2 * dec L u (r / 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (dec_anti L hℓ hsum)
              (by positivity)) hτ
        _ ≤ (1 - u)⁻¹ * ((3 * cL L u ^ 2 + cL L u) * dec L u (r / 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbig hδ) hτ
    · -- `i ≠ j₀`: the slot `j₀` is untouched
      have e0 : (Function.update a i b) 0 = a 0 := Function.update_of_ne (Ne.symm hi) _ _
      have ej : (Function.update a i b) j₀ = a j₀ := Function.update_of_ne (Ne.symm hij) _ _
      have hv := norm_vartheta_le_decay hL hu0 hu1 (Function.update a i b) hj0 (r := r / 2)
        (by rw [e0, ej]; exact hj)
      have hT := norm_T_le hL hu0 hu1 (a i) b
      rw [norm_mul]
      calc ‖thetaGenMat L 1 u (a i) b‖ * ‖vartheta L u (Function.update a i b)‖
          ≤ (1 - u)⁻¹ * (cL L u * dec L u (r / 2)) :=
            mul_le_mul hT hv (norm_nonneg _) hτ
        _ ≤ (1 - u)⁻¹ * ((3 * cL L u ^ 2 + cL L u) * dec L u (r / 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmall hδ) hτ
  · -- slot `0`
    have e0 : (Function.update a 0 x) 0 = x := Function.update_self _ _ _
    have ej : (Function.update a 0 x) j₀ = a j₀ := Function.update_of_ne hj0 _ _
    have hv := norm_vartheta_le_decay hL hu0 hu1 (Function.update a 0 x) hj0
      (r := (zdist2 L (x - a j₀) : ℝ)) (by rw [e0, ej])
    have hT := norm_T_le_decay hL hu0 hu1 (a 0) x
    have htri := zdist2_sub_le L (a 0) x (a j₀)
    have hsum : r / 2 ≤ (zdist2 L (a 0 - x) : ℝ) + (zdist2 L (x - a j₀) : ℝ) := by
      have h' : (zdist2 L (a 0 - a j₀) : ℝ) ≤
          (zdist2 L (a 0 - x) : ℝ) + (zdist2 L (x - a j₀) : ℝ) := by exact_mod_cast htri
      linarith
    rw [norm_mul]
    calc ‖thetaGenMat L 1 u (a 0) x‖ * ‖vartheta L u (Function.update a 0 x)‖
        ≤ ((1 - u)⁻¹ * (3 * cL L u * dec L u (zdist2 L (a 0 - x) : ℝ))) *
            (cL L u * dec L u (zdist2 L (x - a j₀) : ℝ)) :=
          mul_le_mul hT hv (norm_nonneg _) (mul_nonneg hτ (mul_nonneg (mul_nonneg (by norm_num) hC)
            (dec_pos L u _).le))
      _ = (1 - u)⁻¹ * (3 * cL L u ^ 2 * (dec L u (zdist2 L (a 0 - x) : ℝ) *
            dec L u (zdist2 L (x - a j₀) : ℝ))) := by ring
      _ = (1 - u)⁻¹ * (3 * cL L u ^ 2 * dec L u ((zdist2 L (a 0 - x) : ℝ) +
            (zdist2 L (x - a j₀) : ℝ))) := by rw [dec_add]
      _ ≤ (1 - u)⁻¹ * (3 * cL L u ^ 2 * dec L u (r / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (dec_anti L hℓ hsum)
            (by positivity)) hτ
      _ ≤ (1 - u)⁻¹ * ((3 * cL L u ^ 2 + cL L u) * dec L u (r / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbig hδ) hτ

/-- **`K3`** (decay of the kernel in the label spread, all `c`): if `maxDist a ≥ r > 0` then
`|𝔎_{a,c}| ≤ k (1-u)⁻¹ (L² (3c_L² + c_L) + 2 c_L) dec(r/2)`.  (Every term of `𝔎` contains a factor
`Θ_u(a_0, ·)` reaching the far slot `a_{j₀}`, through `ϑ` and `T`.) -/
theorem norm_kerB4_le_far (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a c : Fin k → Z2 L)
    {r : ℝ} (hr : 0 < r) (hfar : r ≤ (KLoop.maxDist L a : ℝ)) :
    ‖kerB4 u a c‖ ≤ ((k : ℝ) * (1 - u)⁻¹ * ((L : ℝ) ^ 2 * (3 * cL L u ^ 2 + cL L u) + 2 * cL L u)) *
      dec L u (r / 2) := by
  obtain ⟨j₀, hj₀S, hj⟩ := exists_far hr hfar
  have hj0 : j₀ ≠ 0 := (Finset.mem_erase.mp hj₀S).1
  obtain ⟨hb1, hb0⟩ := norm_T_vartheta_le_far hL hu0 hu1 a hj0 hj
  have hL1 : 1 ≤ L := by omega
  have h1u : 0 < 1 - u := by linarith
  have hC := cL_nonneg L u
  have hτ : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
  have hδ := (dec_pos L u (r / 2)).le
  set Kc : ℝ := 3 * cL L u ^ 2 + cL L u with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hϑa : ‖vartheta L u a‖ ≤ cL L u * dec L u (r / 2) :=
    norm_vartheta_le_decay hL hu0 hu1 a hj0 hj
  -- `Φ₀`
  have hphi0 : ‖phi0 u a (c 0)‖ ≤ (1 - u)⁻¹ * ((Kc + cL L u) * dec L u (r / 2)) := by
    unfold phi0
    rw [mul_sub]
    refine (norm_sub_le _ _).trans ?_
    have h2 : ‖thetaGenMat L 1 u (a 0) (c 0) * vartheta L u a‖ ≤
        (1 - u)⁻¹ * (cL L u * dec L u (r / 2)) := by
      rw [norm_mul]
      exact mul_le_mul (norm_T_le hL hu0 hu1 _ _) hϑa (norm_nonneg _) hτ
    have h1 := hb0 (c 0)
    calc _ ≤ (1 - u)⁻¹ * (Kc * dec L u (r / 2)) + (1 - u)⁻¹ * (cL L u * dec L u (r / 2)) :=
          add_le_add h1 h2
      _ = (1 - u)⁻¹ * ((Kc + cL L u) * dec L u (r / 2)) := by ring
  -- `Φ₁`
  have hphi1 : ‖phi1 u a‖ ≤ ((k : ℝ) - 1) *
      ((L : ℝ) ^ 2 * ((1 - u)⁻¹ * (Kc * dec L u (r / 2))) + (1 - u)⁻¹ * (cL L u * dec L u (r / 2))) := by
    unfold phi1
    have hterm : ∀ i ∈ Finset.univ.erase (0 : Fin k),
        ‖∑ b, thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b) -
          (((1 - u)⁻¹ : ℝ) : ℂ) * vartheta L u a‖ ≤
        (L : ℝ) ^ 2 * ((1 - u)⁻¹ * (Kc * dec L u (r / 2))) +
          (1 - u)⁻¹ * (cL L u * dec L u (r / 2)) := by
      intro i hi
      have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_sum_le _ _).trans ?_
        calc ∑ b, ‖thetaGenMat L 1 u (a i) b * vartheta L u (Function.update a i b)‖
            ≤ ∑ _b : Z2 L, (1 - u)⁻¹ * (Kc * dec L u (r / 2)) :=
              Finset.sum_le_sum fun b _ => hb1 i b hi0
          _ = (L : ℝ) ^ 2 * ((1 - u)⁻¹ * (Kc * dec L u (r / 2))) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              have : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by
                simp [Z2, ZMod.card]; ring
              rw [this]
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ]
        exact mul_le_mul_of_nonneg_left hϑa hτ
    calc ‖∑ i ∈ Finset.univ.erase (0 : Fin k), _‖
        ≤ ∑ i ∈ Finset.univ.erase (0 : Fin k), ((L : ℝ) ^ 2 * ((1 - u)⁻¹ * (Kc * dec L u (r / 2))) +
          (1 - u)⁻¹ * (cL L u * dec L u (r / 2))) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
      _ = ((k : ℝ) - 1) * ((L : ℝ) ^ 2 * ((1 - u)⁻¹ * (Kc * dec L u (r / 2))) +
          (1 - u)⁻¹ * (cL L u * dec L u (r / 2))) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub (NeZero.pos k)]; simp
          rw [this]
  unfold kerB4
  refine (norm_add_le _ _).trans ?_
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast NeZero.pos k
  have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    nlinarith
  have hind : ‖(if c 0 = a 0 then phi1 u a else 0)‖ ≤ ‖phi1 u a‖ := by
    split_ifs
    · exact le_rfl
    · simp
  have hδτ : 0 ≤ (1 - u)⁻¹ * dec L u (r / 2) := mul_nonneg hτ hδ
  calc ‖phi0 u a (c 0)‖ + ‖(if c 0 = a 0 then phi1 u a else 0)‖
      ≤ (1 - u)⁻¹ * ((Kc + cL L u) * dec L u (r / 2)) +
        ((k : ℝ) - 1) * ((L : ℝ) ^ 2 * ((1 - u)⁻¹ * (Kc * dec L u (r / 2))) +
          (1 - u)⁻¹ * (cL L u * dec L u (r / 2))) := add_le_add hphi0 (hind.trans hphi1)
    _ ≤ ((k : ℝ) * (1 - u)⁻¹ * ((L : ℝ) ^ 2 * Kc + 2 * cL L u)) * dec L u (r / 2) := by
        have e : (1 - u)⁻¹ * ((Kc + cL L u) * dec L u (r / 2)) +
            ((k : ℝ) - 1) * ((L : ℝ) ^ 2 * ((1 - u)⁻¹ * (Kc * dec L u (r / 2))) +
              (1 - u)⁻¹ * (cL L u * dec L u (r / 2))) =
            ((1 - u)⁻¹ * dec L u (r / 2)) * ((Kc + cL L u) +
              ((k : ℝ) - 1) * ((L : ℝ) ^ 2 * Kc + cL L u)) := by ring
        rw [e]
        have e2 : ((k : ℝ) * (1 - u)⁻¹ * ((L : ℝ) ^ 2 * Kc + 2 * cL L u)) * dec L u (r / 2) =
            ((1 - u)⁻¹ * dec L u (r / 2)) * ((k : ℝ) * ((L : ℝ) ^ 2 * Kc + 2 * cL L u)) := by ring
        rw [e2]
        refine mul_le_mul_of_nonneg_left ?_ hδτ
        nlinarith [mul_nonneg (sub_nonneg.2 hL2) hKc0, mul_nonneg (sub_nonneg.2 hk1) hKc0,
          mul_nonneg (sub_nonneg.2 hk1) hC, mul_nonneg (sub_nonneg.2 hk1) (mul_nonneg (sub_nonneg.2 hL2) hKc0)]

end KernelB4

section Assembly

variable {L W : ℕ} [NeZero L] [NeZero W] {k k' K : ℕ} [NeZero k] [NeZero k']

/-- The kernel truncated to `maxDist a < ρ` and `|c₀ - a₀| < ρ`. -/
def kerTrunc (ρ : ℝ) (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (a : Fin k' → Z2 L)
    (c : Fin k → Z2 L) : ℂ :=
  if (KLoop.maxDist L a : ℝ) < ρ ∧ ((zdist2 L (c 0 - a 0) : ℕ) : ℝ) < ρ then 𝔎 a c else 0

/-- The tensor truncated to `maxDist c < ρ`. -/
def tensTrunc (ρ : ℝ) (X : (Fin k → Z2 L) → ℂ) (c : Fin k → Z2 L) : ℂ :=
  if (KLoop.maxDist L c : ℝ) < ρ then X c else 0

/-- The `ℓ¹` norm of the far part of a tensor: `Σ_c |X_c| 1(maxDist c ≥ ρ)`. -/
def l1far (ρ : ℝ) (X : (Fin k → Z2 L) → ℂ) : ℝ :=
  ∑ c : Fin k → Z2 L, ‖X c‖ * (if ρ ≤ (KLoop.maxDist L c : ℝ) then 1 else 0)

/-- `l1far ≥ 0`. -/
theorem l1far_nonneg (ρ : ℝ) (X : (Fin k → Z2 L) → ℂ) : 0 ≤ l1far ρ X :=
  Finset.sum_nonneg fun c _ => mul_nonneg (norm_nonneg _) (by split_ifs <;> norm_num)

/-- `Qop` is linear (subtraction). -/
theorem qop_sub (u : ℝ) (A B : (Fin k' → Z2 L) → ℂ) (a : Fin k' → Z2 L) :
    Qop L u A a - Qop L u B a = Qop L u (fun a' => A a' - B a') a := by
  unfold Qop Psum
  rw [Finset.sum_sub_distrib]
  ring

/-- **The pointwise truncation error** `R_a = Σ_c 𝔎_{a,c} X_c - Σ_c 𝔎^{tr}_{a,c} X^{tr}_c` is at most
`|{c}| δ B_X + B_𝔎 · l1far(X)`. -/
theorem norm_trunc_error_le (ρ : ℝ) (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ)
    (X : (Fin k → Z2 L) → ℂ) {B_K B_X δ : ℝ} (hBK : 0 ≤ B_K) (hBX : 0 ≤ B_X) (hδ : 0 ≤ δ)
    (hK1 : ∀ a c, ‖𝔎 a c‖ ≤ B_K)
    (hK2 : ∀ a c, ρ ≤ (zdist2 L (c 0 - a 0) : ℝ) → (KLoop.maxDist L c : ℝ) < ρ → ‖𝔎 a c‖ ≤ δ)
    (hK3 : ∀ a c, ρ ≤ (KLoop.maxDist L a : ℝ) → (KLoop.maxDist L c : ℝ) < ρ → ‖𝔎 a c‖ ≤ δ)
    (hX : ∀ c, ‖X c‖ ≤ B_X) (a : Fin k' → Z2 L) :
    ‖(∑ c, 𝔎 a c * X c) - ∑ c, kerTrunc ρ 𝔎 a c * tensTrunc ρ X c‖ ≤
      ((L : ℝ) ^ 2) ^ k * δ * B_X + B_K * l1far ρ X := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c : Fin k → Z2 L,
      ‖𝔎 a c * X c - kerTrunc ρ 𝔎 a c * tensTrunc ρ X c‖ ≤
        δ * B_X + B_K * (‖X c‖ * (if ρ ≤ (KLoop.maxDist L c : ℝ) then 1 else 0)) := by
    intro c
    by_cases hc : (KLoop.maxDist L c : ℝ) < ρ
    · have hcf : ¬ (ρ ≤ (KLoop.maxDist L c : ℝ)) := not_le.mpr hc
      simp only [tensTrunc, hc, ↓reduceIte, hcf, mul_zero, add_zero]
      by_cases hg : (KLoop.maxDist L a : ℝ) < ρ ∧ ((zdist2 L (c 0 - a 0) : ℕ) : ℝ) < ρ
      · simp only [kerTrunc, hg, and_self, ↓reduceIte, sub_self, norm_zero]
        positivity
      · have h0 : kerTrunc ρ 𝔎 a c = 0 := by simp [kerTrunc, hg]
        rw [h0, zero_mul, sub_zero, norm_mul]
        have hbd : ‖𝔎 a c‖ ≤ δ := by
          by_cases h1 : (KLoop.maxDist L a : ℝ) < ρ
          · have h2 : ρ ≤ ((zdist2 L (c 0 - a 0) : ℕ) : ℝ) := by
              by_contra h2
              exact hg ⟨h1, not_le.mp h2⟩
            exact hK2 a c h2 hc
          · exact hK3 a c (not_lt.mp h1) hc
        exact mul_le_mul hbd (hX c) (norm_nonneg _) hδ
    · have hcf : ρ ≤ (KLoop.maxDist L c : ℝ) := not_lt.mp hc
      simp only [tensTrunc, hc, ↓reduceIte, hcf, mul_zero, sub_zero, mul_one]
      rw [norm_mul]
      calc ‖𝔎 a c‖ * ‖X c‖ ≤ B_K * ‖X c‖ := mul_le_mul_of_nonneg_right (hK1 a c) (norm_nonneg _)
        _ ≤ δ * B_X + B_K * ‖X c‖ := by nlinarith [mul_nonneg hδ hBX]
  calc ∑ c, ‖𝔎 a c * X c - kerTrunc ρ 𝔎 a c * tensTrunc ρ X c‖
      ≤ ∑ c : Fin k → Z2 L, (δ * B_X + B_K * (‖X c‖ * (if ρ ≤ (KLoop.maxDist L c : ℝ) then 1 else 0))) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = ((L : ℝ) ^ 2) ^ k * δ * B_X + B_K * l1far ρ X := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_labels,
          ← Finset.mul_sum]
        unfold l1far
        ring

/-- **The error of the truncated kernel form after `𝒬_u`**: for every label `a`,
`|(𝒬_u 𝔎X)_a - (𝒬_u 𝔎^{tr}X^{tr})_a| ≤ (1 + |{a'}|)(|{c}| δ B_X + B_𝔎 l1far(X))`. -/
theorem norm_qop_error_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ρ : ℝ)
    (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (X : (Fin k → Z2 L) → ℂ) {B_K B_X δ : ℝ}
    (hBK : 0 ≤ B_K) (hBX : 0 ≤ B_X) (hδ : 0 ≤ δ) (hK1 : ∀ a c, ‖𝔎 a c‖ ≤ B_K)
    (hK2 : ∀ a c, ρ ≤ (zdist2 L (c 0 - a 0) : ℝ) → (KLoop.maxDist L c : ℝ) < ρ → ‖𝔎 a c‖ ≤ δ)
    (hK3 : ∀ a c, ρ ≤ (KLoop.maxDist L a : ℝ) → (KLoop.maxDist L c : ℝ) < ρ → ‖𝔎 a c‖ ≤ δ)
    (hX : ∀ c, ‖X c‖ ≤ B_X) (a : Fin k' → Z2 L) :
    ‖Qop L u (fun a' => ∑ c, 𝔎 a' c * X c) a -
        Qop L u (fun a' => ∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c) a‖ ≤
      (1 + ((L : ℝ) ^ 2) ^ k') * (((L : ℝ) ^ 2) ^ k * δ * B_X + B_K * l1far ρ X) := by
  rw [qop_sub]
  set Rb : ℝ := ((L : ℝ) ^ 2) ^ k * δ * B_X + B_K * l1far ρ X with hRb
  have hR : ∀ a' : Fin k' → Z2 L,
      ‖(∑ c, 𝔎 a' c * X c) - ∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c‖ ≤ Rb :=
    fun a' => norm_trunc_error_le ρ 𝔎 X hBK hBX hδ hK1 hK2 hK3 hX a'
  have hRb0 : 0 ≤ Rb := (norm_nonneg _).trans (hR a)
  unfold Qop
  refine (norm_sub_le _ _).trans ?_
  have h1 := hR a
  have h2 : ‖Psum L (fun a' => (∑ c, 𝔎 a' c * X c) - ∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c)
      (a 0) * vartheta L u a‖ ≤ ((L : ℝ) ^ 2) ^ k' * Rb := by
    rw [norm_mul]
    have hϑ := norm_vartheta_le_one hL hu0 hu1 a
    have hP : ‖Psum L (fun a' => (∑ c, 𝔎 a' c * X c) - ∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c)
        (a 0)‖ ≤ ((L : ℝ) ^ 2) ^ k' * Rb := by
      unfold Psum
      refine (norm_sum_le _ _).trans ?_
      calc ∑ a' ∈ Finset.univ.filter (fun a' : Fin k' → Z2 L => a' 0 = a 0),
            ‖(∑ c, 𝔎 a' c * X c) - ∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c‖
          ≤ ∑ a' ∈ Finset.univ.filter (fun a' : Fin k' → Z2 L => a' 0 = a 0), Rb :=
            Finset.sum_le_sum fun a' _ => hR a'
        _ ≤ ∑ _a' : Fin k' → Z2 L, Rb :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => hRb0
        _ = ((L : ℝ) ^ 2) ^ k' * Rb := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_labels]
    calc _ ≤ (((L : ℝ) ^ 2) ^ k' * Rb) * 1 := mul_le_mul hP hϑ (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  linarith

/-! ### The assembled form -/

/-- **The assembled form** `𝒬_u(𝔎^{tr} F^{tr})`: truncate the source form to `maxDist c < ρ`, apply the
truncated kernel, then `𝒬_u` on the coefficients. -/
def asmF (u ρ : ℝ) (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (FX : LocalForm L W k K) :
    LocalForm L W k' K :=
  qopF u (kerApply (kerTrunc ρ 𝔎) (truncF ρ FX))

/-- The assembled form evaluates to `𝒬_u` of the truncated kernel applied to the truncated tensor. -/
theorem eval_asmF (u ρ : ℝ) (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (FX : LocalForm L W k K)
    (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (X : (Fin k → Z2 L) → ℂ)
    (hFX : ∀ c, FX.eval E s M c = X c) (a : Fin k' → Z2 L) :
    (asmF u ρ 𝔎 FX).eval E s M a =
      Qop L u (fun a' => ∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c) a := by
  unfold asmF
  rw [eval_qopF]
  have h : (kerApply (kerTrunc ρ 𝔎) (truncF ρ FX)).eval E s M =
      fun a' => ∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c := by
    funext a'
    rw [eval_kerApply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [eval_truncF, hFX c]
    rfl
  rw [h]

/-- Truncating a kernel keeps the entrywise bound. -/
theorem norm_kerTrunc_le (ρ : ℝ) (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) {B_K : ℝ}
    (hBK : 0 ≤ B_K) (hK1 : ∀ a c, ‖𝔎 a c‖ ≤ B_K) (a : Fin k' → Z2 L) (c : Fin k → Z2 L) :
    ‖kerTrunc ρ 𝔎 a c‖ ≤ B_K := by
  unfold kerTrunc
  split_ifs
  · exact hK1 a c
  · simpa using hBK

/-- The coefficient bound of the assembled form. -/
theorem coef_asmF_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ρ : ℝ)
    (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (FX : LocalForm L W k K) {B B_K : ℝ}
    (hB : 0 ≤ B) (hBK : 0 ≤ B_K) (hF : ∀ c j q, ‖FX.coef c j q‖ ≤ B) (hK1 : ∀ a c, ‖𝔎 a c‖ ≤ B_K)
    (a : Fin k' → Z2 L) (j : Fin (K + 1)) (q : Fin j → Mono L W) :
    ‖(asmF u ρ 𝔎 FX).coef a j q‖ ≤
      (1 + ((L : ℝ) ^ 2) ^ k') * (((L : ℝ) ^ 2) ^ k * B_K * B) := by
  unfold asmF
  refine coef_qopF_le u _ (B := ((L : ℝ) ^ 2) ^ k * B_K * B) (by positivity)
    (fun c' j' q' => ?_) (fun a' => norm_vartheta_le_one hL hu0 hu1 a') a j q
  refine coef_kerApply_le (kerTrunc ρ 𝔎) (truncF ρ FX) hB (coef_truncF_le ρ FX hB hF)
    (B𝔎 := ((L : ℝ) ^ 2) ^ k * B_K) (fun a' => ?_) c' j' q'
  calc ∑ c, ‖kerTrunc ρ 𝔎 a' c‖ ≤ ∑ _c : Fin k → Z2 L, B_K :=
        Finset.sum_le_sum fun c _ => norm_kerTrunc_le ρ 𝔎 hBK hK1 a' c
    _ = ((L : ℝ) ^ 2) ^ k * B_K := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_labels]

/-- The locality of the assembled form: `Loc0 R₀` of the truncated source becomes `Loc0 (R₀ + 2ρ)`. -/
theorem loc0_asmF (u ρ : ℝ) (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (FX : LocalForm L W k K)
    {R₀ : ℝ} (hF : Loc0 R₀ (truncF ρ FX)) : Loc0 (R₀ + 2 * ρ) (asmF u ρ 𝔎 FX) := by
  unfold asmF
  refine loc0_qopF u _ (loc0_kerApply (kerTrunc ρ 𝔎) (truncF ρ FX) hF (fun a c hne => ?_))
  by_contra hlt
  apply hne
  have hn : ¬ ((KLoop.maxDist L a : ℝ) < ρ ∧ ((zdist2 L (c 0 - a 0) : ℕ) : ℝ) < ρ) :=
    fun ⟨_, h2⟩ => hlt h2
  simp [kerTrunc, hn]

/-- The assembled form is sum-zero for every matrix. -/
theorem sumZero_asmF (hL : 3 ≤ L) (hk' : 2 ≤ k') {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ρ : ℝ)
    (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (FX : LocalForm L W k K) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) :
    SumZero L (fun b => (asmF u ρ 𝔎 FX).eval E s M b) :=
  sumZero_qopF hL hk' hu0 hu1 _ E s M

/-- **The far label decay of the assembled form is deterministic**: at a label `b` with
`maxDist b ≥ ρ` the truncated kernel vanishes, so only the `ϑ` part of `𝒬_u` remains. -/
theorem norm_eval_asmF_le_far (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ρ : ℝ)
    (𝔎 : (Fin k' → Z2 L) → (Fin k → Z2 L) → ℂ) (FX : LocalForm L W k K) (E s : ℝ)
    (M : Matrix (Idx L W) (Idx L W) ℂ) (X : (Fin k → Z2 L) → ℂ)
    (hFX : ∀ c, FX.eval E s M c = X c) {B_K B_X : ℝ} (hBK : 0 ≤ B_K) (hBX : 0 ≤ B_X)
    (hK1 : ∀ a c, ‖𝔎 a c‖ ≤ B_K) (hX : ∀ c, ‖X c‖ ≤ B_X) (b : Fin k' → Z2 L)
    (hb : ρ ≤ (KLoop.maxDist L b : ℝ)) :
    ‖(asmF u ρ 𝔎 FX).eval E s M b‖ ≤
      (((L : ℝ) ^ 2) ^ k' * (((L : ℝ) ^ 2) ^ k * B_K * B_X)) * ‖vartheta L u b‖ := by
  rw [eval_asmF u ρ 𝔎 FX E s M X hFX b]
  unfold Qop
  beta_reduce
  have hT0 : (∑ c, kerTrunc ρ 𝔎 b c * tensTrunc ρ X c) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have hn : ¬ ((KLoop.maxDist L b : ℝ) < ρ ∧ ((zdist2 L (c 0 - b 0) : ℕ) : ℝ) < ρ) :=
      fun ⟨h1, _⟩ => absurd hb (not_le.mpr h1)
    have : kerTrunc ρ 𝔎 b c = 0 := by simp [kerTrunc, hn]
    rw [this, zero_mul]
  rw [hT0, zero_sub, norm_neg, norm_mul]
  have hT : ∀ a' : Fin k' → Z2 L,
      ‖∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c‖ ≤ ((L : ℝ) ^ 2) ^ k * B_K * B_X := by
    intro a'
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c, ‖kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c‖ ≤ ∑ _c : Fin k → Z2 L, B_K * B_X :=
          Finset.sum_le_sum fun c _ => by
            rw [norm_mul]
            refine mul_le_mul (norm_kerTrunc_le ρ 𝔎 hBK hK1 a' c) ?_ (norm_nonneg _) hBK
            unfold tensTrunc
            split_ifs
            · exact hX c
            · simpa using hBX
      _ = ((L : ℝ) ^ 2) ^ k * B_K * B_X := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_labels]
          ring
  have hP : ‖Psum L (fun a' => ∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c) (b 0)‖ ≤
      ((L : ℝ) ^ 2) ^ k' * (((L : ℝ) ^ 2) ^ k * B_K * B_X) := by
    unfold Psum
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a' ∈ Finset.univ.filter (fun a' : Fin k' → Z2 L => a' 0 = b 0),
          ‖∑ c, kerTrunc ρ 𝔎 a' c * tensTrunc ρ X c‖
        ≤ ∑ a' ∈ Finset.univ.filter (fun a' : Fin k' → Z2 L => a' 0 = b 0),
            ((L : ℝ) ^ 2) ^ k * B_K * B_X := Finset.sum_le_sum fun a' _ => hT a'
      _ ≤ ∑ _a' : Fin k' → Z2 L, ((L : ℝ) ^ 2) ^ k * B_K * B_X :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
      _ = ((L : ℝ) ^ 2) ^ k' * (((L : ℝ) ^ 2) ^ k * B_K * B_X) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_labels]
  exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)

end Assembly

section Stochastic

variable (d : Sizes)

private theorem transport_real {P Q e f γ ξ η A S : ℝ} (hPQ : P = Q * Q) (hQ : 2 ≤ Q) (hf : 0 ≤ f)
    (hη : 0 ≤ η) (hS : 0 < S) (hAS : A ≤ S) (hA : 0 ≤ A) (hef : e = f * S) (hγ : γ ≤ e / 2)
    (hξ : ξ ≤ γ + A * η) (hev : P * e < ξ) : Q * f < η := by
  have hP : 2 * Q ≤ P := by rw [hPQ]; nlinarith
  have h1 : (P - 1 / 2) * e < A * η := by nlinarith
  have h2 : A * η ≤ S * η := mul_le_mul_of_nonneg_right hAS hη
  have h3 : (P - 1 / 2) * f * S < η * S := by rw [hef] at h1; nlinarith
  have h4 : (P - 1 / 2) * f < η := by
    by_contra h
    push Not at h
    nlinarith
  have h5 : Q * f ≤ (P - 1 / 2) * f := by
    have : Q ≤ P - 1 / 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hf
  linarith

/-- **Closure lemma (g), error transport.**  Let `η ≥ 0` be an error that is `O_≺(W^{-D})` per time
(`PerTimeDomAt`).  If `ξ ≤ γ + N^C η` pointwise, with `γ ≤ ½ W^{-(D - C/c)}` eventually (a
deterministic tail; a linear map of norm `≤ N^C` applied to `η` is of this form), then `ξ` is
`O_≺(W^{-(D - C/c)})` per time (`Bandwidth`: `N^C ≤ W^{C/c}`). -/
theorem errTransport {c C D : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hband : Bandwidth d c)
    (hsize : SizeTendsto d) {U : ℕ → Type*} {η ξ : ∀ n, U n → Sizes.SeqΩ d → ℝ} {γ : ℕ → ℝ}
    (hη0 : ∀ n p ω, 0 ≤ η n p ω)
    (hη : PerTimeDomAt (Sizes.seqP d) d.size η (fun n _ _ => (d.W n : ℝ) ^ (-D)))
    (hγ : ∀ᶠ n : ℕ in atTop, γ n ≤ (d.W n : ℝ) ^ (-(D - C / c)) / 2)
    (hξ : ∀ᶠ n : ℕ in atTop, ∀ p ω, ξ n p ω ≤ γ n + ((d.size n : ℕ) : ℝ) ^ C * η n p ω) :
    PerTimeDomAt (Sizes.seqP d) d.size ξ (fun n _ _ => (d.W n : ℝ) ^ (-(D - C / c))) := by
  intro τ hτ D' hD'
  have h1 := hη (τ / 2) (half_pos hτ) D' hD'
  have h2 : ∀ᶠ n : ℕ in atTop, 2 ≤ ((d.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop 2
  filter_upwards [h1, hband, hγ, h2, hsize.eventually_ge_atTop 1, hξ] with n h1n hb hg h2n hN1 hξn p
  refine le_trans (measure_mono ?_) (h1n p)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  set Nr : ℝ := ((d.size n : ℕ) : ℝ) with hNr
  set Wr : ℝ := (d.W n : ℝ) with hWr
  have hN0 : 0 < Nr := by linarith
  have hW0 : 0 < Wr := by
    have := d.W_pos n
    rw [hWr]; exact_mod_cast this
  have hNC : Nr ^ C ≤ Wr ^ (C / c) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le c) hb (div_nonneg hC hc.le)
    rwa [← Real.rpow_mul hN0.le, mul_div_cancel₀ _ hc.ne'] at h
  have hPQ : Nr ^ τ = Nr ^ (τ / 2) * Nr ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hef : Wr ^ (-(D - C / c)) = Wr ^ (-D) * Wr ^ (C / c) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  exact transport_real hPQ h2n (Real.rpow_nonneg hW0.le _) (hη0 n p ω) (Real.rpow_pos_of_pos hW0 _)
    hNC (Real.rpow_nonneg hN0.le _) hef hg (hξn p ω) hω

/-- `N ≥ 9` for every admissible size. -/
theorem size_ge_nine (n : ℕ) : 9 ≤ d.size n := by
  rw [Sizes.size_eq]
  have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
  have h2 : 9 ≤ d.L n ^ 2 := by
    have := d.three_le_L n
    nlinarith
  calc 9 = 1 * 9 := by norm_num
    _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 h2

/-- **A deterministic pointwise bound is a `≺`** (as `perTimeDomAt_const`, with the
parameter- and sample-dependent control). -/
theorem perTimeDomAt_of_le {U : ℕ → Type*} {ξ ζ : ∀ n, U n → Sizes.SeqΩ d → ℝ}
    (hζ : ∀ n p ω, 0 ≤ ζ n p ω) (hle : ∀ᶠ n : ℕ in atTop, ∀ p ω, ξ n p ω ≤ ζ n p ω) :
    PerTimeDomAt (Sizes.seqP d) d.size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [hle] with n hn p
  have hs : (1 : ℝ) ≤ (d.size n : ℝ) := by
    have := size_ge_nine d n
    exact_mod_cast (by omega : 1 ≤ d.size n)
  have h1 : (1 : ℝ) ≤ (d.size n : ℝ) ^ τ := Real.one_le_rpow hs hτ.le
  have hsub : {ω : Sizes.SeqΩ d | (d.size n : ℝ) ^ τ * ζ n p ω < ξ n p ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    nlinarith [hζ n p ω, hn p ω]
  rw [hsub, measure_empty]
  exact zero_le

/-- `W_n → ∞` from `Bandwidth` and `SizeTendsto`. -/
theorem tendsto_W_atTop {c : ℝ} (hc : 0 < c) (hband : Bandwidth d c) (hsize : SizeTendsto d) :
    Tendsto (fun n => (d.W n : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun n => ((d.size n : ℕ) : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp hsize
  exact tendsto_atTop_mono' atTop hband h1

/-- `N^a ≤ W^{a/c}` from `N^c ≤ W`. -/
theorem N_pow_le_W_pow {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (n : ℕ)
    (hb : ((d.size n : ℕ) : ℝ) ^ c ≤ (d.W n : ℝ)) :
    ((d.size n : ℕ) : ℝ) ^ a ≤ (d.W n : ℝ) ^ (a / c) := by
  have hN0 : 0 ≤ ((d.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hN0 c) hb (div_nonneg ha hc.le)
  rwa [← Real.rpow_mul hN0, mul_div_cancel₀ _ hc.ne'] at h

/-- **Exponential beats every power**: `N^a exp(-W^{τ₀}/c₀) ≤ W^{-b}` eventually
(`Bandwidth`: `N^a ≤ W^{a/c}`; `x^s e^{-x/c₀} → 0`). -/
theorem tail_eventually {c a b c₀ τ₀ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hc₀ : 0 < c₀) (hτ₀ : 0 < τ₀)
    (hband : Bandwidth d c) (hsize : SizeTendsto d) :
    ∀ᶠ n : ℕ in atTop,
      ((d.size n : ℕ) : ℝ) ^ a * Real.exp (-((d.W n : ℝ) ^ τ₀ / c₀)) ≤ (d.W n : ℝ) ^ (-b) := by
  have hW := tendsto_W_atTop d hc hband hsize
  set s : ℝ := (a / c + b) / τ₀ with hs
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s (1 / c₀) (by positivity)
  have h1 : ∀ᶠ x : ℝ in atTop, x ^ s * Real.exp (-(1 / c₀) * x) ≤ 1 :=
    h0.eventually (ge_mem_nhds zero_lt_one)
  have hx : Tendsto (fun n => (d.W n : ℝ) ^ τ₀) atTop atTop := (tendsto_rpow_atTop hτ₀).comp hW
  filter_upwards [hx.eventually h1, hband, hW.eventually_ge_atTop 1] with n hn hb hW1
  have hW0 : 0 < (d.W n : ℝ) := by linarith
  have hexp : Real.exp (-((d.W n : ℝ) ^ τ₀ / c₀)) = Real.exp (-(1 / c₀) * (d.W n : ℝ) ^ τ₀) := by
    congr 1; ring
  rw [hexp]
  have hpow : ((d.W n : ℝ) ^ τ₀) ^ s = (d.W n : ℝ) ^ (a / c + b) := by
    rw [← Real.rpow_mul hW0.le, hs]
    congr 1
    field_simp
  rw [hpow] at hn
  have hNa := N_pow_le_W_pow d hc ha n hb
  have hE0 : 0 ≤ Real.exp (-(1 / c₀) * (d.W n : ℝ) ^ τ₀) := (Real.exp_pos _).le
  calc ((d.size n : ℕ) : ℝ) ^ a * Real.exp (-(1 / c₀) * (d.W n : ℝ) ^ τ₀)
      ≤ (d.W n : ℝ) ^ (a / c) * Real.exp (-(1 / c₀) * (d.W n : ℝ) ^ τ₀) :=
        mul_le_mul_of_nonneg_right hNa hE0
    _ ≤ (d.W n : ℝ) ^ (-b) := by
        have hb0 : 0 < (d.W n : ℝ) ^ b := Real.rpow_pos_of_pos hW0 b
        have e : (d.W n : ℝ) ^ (-b) = ((d.W n : ℝ) ^ b)⁻¹ := Real.rpow_neg hW0.le b
        rw [e, ← one_div, le_div_iff₀ hb0]
        calc (d.W n : ℝ) ^ (a / c) * Real.exp (-(1 / c₀) * (d.W n : ℝ) ^ τ₀) * (d.W n : ℝ) ^ b
            = (d.W n : ℝ) ^ (a / c + b) * Real.exp (-(1 / c₀) * (d.W n : ℝ) ^ τ₀) := by
              rw [Real.rpow_add hW0]; ring
          _ ≤ 1 := hn

/-- `L² ≤ N`. -/
theorem L_sq_le_size (n : ℕ) : ((d.L n : ℝ)) ^ 2 ≤ ((d.size n : ℕ) : ℝ) := by
  have h1 : 1 ≤ d.W n ^ 2 := Nat.one_le_pow _ _ (d.W_pos n)
  have h : d.L n ^ 2 ≤ d.size n := by
    rw [Sizes.size_eq]
    calc d.L n ^ 2 = 1 * d.L n ^ 2 := by ring
      _ ≤ d.W n ^ 2 * d.L n ^ 2 := Nat.mul_le_mul h1 le_rfl
  exact_mod_cast h

/-- **Closure lemma (a), the union over labels (generic)**: let `X_n(ω)` be a `k`-tensor whose far part
is small label by label, `|X_c| 1(ρ_n ≤ maxDist c) ≺ W^{-(D + k/c)}` per time.  Then its far part in `ℓ¹`
over the `≤ N^k` labels is `≺ W^{-D}` (`N^k ≤ W^{k/c}` by `Bandwidth`). -/
theorem l1far_PT {c D : ℝ} (hc : 0 < c) (hband : Bandwidth d c) {k : ℕ} [NeZero k]
    {X : ∀ n, Sizes.SeqΩ d → (Fin k → Z2 (d.L n)) → ℂ} {ρ : ℕ → ℝ}
    (h : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
      (fun n p ω => ‖X n ω p.2‖ * (if ρ n ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) then 1 else 0))
      (fun n _ _ => (d.W n : ℝ) ^ (-(D + (k : ℝ) / c)))) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun _ => Unit)
      (fun n _ ω => l1far (ρ n) (X n ω)) (fun n _ _ => (d.W n : ℝ) ^ (-D)) := by
  intro τ' hτ' D₁ hD₁
  have hk0 : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  have h1 := h τ' hτ' (D₁ + k) (by linarith)
  filter_upwards [h1, hband] with n h1n hb p
  set Nr : ℝ := ((d.size n : ℕ) : ℝ) with hNr
  set Wr : ℝ := (d.W n : ℝ) with hWr
  have hN1 : (1 : ℝ) ≤ Nr := by
    have := size_ge_nine d n
    rw [hNr]; exact_mod_cast (by omega : 1 ≤ d.size n)
  have hN0 : 0 < Nr := by linarith
  have hW0 : 0 < Wr := by
    have := d.W_pos n
    rw [hWr]; exact_mod_cast this
  set Dfar : ℝ := D + (k : ℝ) / c with hDfar
  let B : (Fin k → Z2 (d.L n)) → Set (Sizes.SeqΩ d) := fun c' =>
    {ω | Nr ^ τ' * Wr ^ (-Dfar) <
      ‖X n ω c'‖ * (if ρ n ≤ (KLoop.maxDist (d.L n) c' : ℝ) then 1 else 0)}
  have hBc : ∀ c', Sizes.seqP d (B c') ≤ ENNReal.ofReal (Nr ^ (-(D₁ + k))) := fun c' =>
    h1n ((), c')
  have hsub : {ω | Nr ^ τ' * Wr ^ (-D) < l1far (ρ n) (X n ω)} ⊆ ⋃ c', B c' := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hno
    have hall : ∀ c', ‖X n ω c'‖ * (if ρ n ≤ (KLoop.maxDist (d.L n) c' : ℝ) then 1 else 0) ≤
        Nr ^ τ' * Wr ^ (-Dfar) := by
      intro c'
      by_contra hc'
      exact hno (Set.mem_iUnion.mpr ⟨c', by simpa [B] using not_le.mp hc'⟩)
    have hsum : l1far (ρ n) (X n ω) ≤ Nr ^ τ' * Wr ^ (-D) := by
      calc l1far (ρ n) (X n ω)
          ≤ ∑ _c' : Fin k → Z2 (d.L n), Nr ^ τ' * Wr ^ (-Dfar) := Finset.sum_le_sum fun c' _ => hall c'
        _ = (((d.L n : ℝ) ^ 2) ^ k) * (Nr ^ τ' * Wr ^ (-Dfar)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_labels]
        _ ≤ Nr ^ (k : ℝ) * (Nr ^ τ' * Wr ^ (-Dfar)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [Real.rpow_natCast]
            exact pow_le_pow_left₀ (by positivity) (L_sq_le_size d n) k
        _ ≤ Wr ^ ((k : ℝ) / c) * (Nr ^ τ' * Wr ^ (-Dfar)) :=
            mul_le_mul_of_nonneg_right (N_pow_le_W_pow d hc (Nat.cast_nonneg k) n hb)
              (by positivity)
        _ = Nr ^ τ' * Wr ^ (-D) := by
            have : Wr ^ ((k : ℝ) / c) * Wr ^ (-Dfar) = Wr ^ (-D) := by
              rw [← Real.rpow_add hW0]; congr 1; rw [hDfar]; ring
            calc Wr ^ ((k : ℝ) / c) * (Nr ^ τ' * Wr ^ (-Dfar))
                = Nr ^ τ' * (Wr ^ ((k : ℝ) / c) * Wr ^ (-Dfar)) := by ring
              _ = Nr ^ τ' * Wr ^ (-D) := by rw [this]
    exact absurd (lt_of_lt_of_le hω hsum) (lt_irrefl _)
  calc Sizes.seqP d {ω | Nr ^ τ' * Wr ^ (-D) < l1far (ρ n) (X n ω)}
      ≤ Sizes.seqP d (⋃ c', B c') := measure_mono hsub
    _ ≤ ∑ c', Sizes.seqP d (B c') := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _c' : Fin k → Z2 (d.L n), ENNReal.ofReal (Nr ^ (-(D₁ + k))) :=
        Finset.sum_le_sum fun c' _ => hBc c'
    _ = ENNReal.ofReal ((((d.L n : ℝ) ^ 2) ^ k) * Nr ^ (-(D₁ + k))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← card_labels, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Nr ^ (-D₁)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : (((d.L n : ℝ) ^ 2) ^ k) ≤ Nr ^ (k : ℝ) := by
          rw [Real.rpow_natCast]
          exact pow_le_pow_left₀ (by positivity) (L_sq_le_size d n) k
        calc (((d.L n : ℝ) ^ 2) ^ k) * Nr ^ (-(D₁ + k)) ≤ Nr ^ (k : ℝ) * Nr ^ (-(D₁ + k)) :=
              mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = Nr ^ (-D₁) := by
              rw [← Real.rpow_add hN0]; congr 1; ring

/-- **Closure lemma (a): the truncation of the loop tensor `𝓛 - 𝒦` to `maxDist c < ρ`,
`ρ = ℓ_u W^{τ₀}/8`, costs `O_≺(W^{-D})` in `ℓ¹` over the labels**, for every `D > 0`: from `DecayLoopPT`
(the far labels `max|c_i - c_j| ≥ ℓ_u W^{τ₀/2}` carry `|𝓛| + |𝓛 - 𝒦| ≺ W^{-D'}`, `D' = D + k/c`) and the
union `l1far_PT` over the `≤ N^k` labels (`W^{τ₀/2} ≥ 8` eventually, so `ρ ≥ ℓ_u W^{τ₀/2}`). -/
theorem lkTruncErr {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hdl : DecayLoopPT d E s t) {k : ℕ} [NeZero k] (hk : 1 ≤ k) {τ₀ D : ℝ} (hτ₀ : 0 < τ₀)
    (hD : 0 < D) (u : ℕ → ℝ) (σ : ∀ n, Fin k → Bool) (hu : ∀ n, s n ≤ u n)
    (hut : ∀ n, u n ≤ t n) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun _ => Unit)
      (fun n _ ω => l1far (ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8)
        (lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n)))
      (fun n _ _ => (d.W n : ℝ) ^ (-D)) := by
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain
  have hkc : 0 < (k : ℝ) / c := by
    have : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
    positivity
  refine l1far_PT d hc hband (D := D) (fun τ' hτ' D₁ hD₁ => ?_)
  have h1 := hdl k hk (τ₀ / 2) (half_pos hτ₀) (D + (k : ℝ) / c) (by linarith) τ' hτ' D₁ hD₁
  have hW := tendsto_W_atTop d hc hband hsize
  have e8 : ∀ᶠ n : ℕ in atTop, 8 ≤ (d.W n : ℝ) ^ (τ₀ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ₀)).comp hW).eventually_ge_atTop 8
  filter_upwards [h1, e8] with n h1n h8 p
  have hu1 : u n < 1 := lt_of_le_of_lt (hut n) (ht1 n)
  have hℓ : 0 < ellT (d.L n) (u n) := (ellT_pos_le (by have := d.three_le_L n; omega) hu1).1
  have hW0 : 0 < (d.W n : ℝ) := by exact_mod_cast d.W_pos n
  -- the far windows are nested
  have hnest : ellT (d.L n) (u n) * (d.W n : ℝ) ^ (τ₀ / 2) ≤
      ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8 := by
    have hpow : (d.W n : ℝ) ^ τ₀ = (d.W n : ℝ) ^ (τ₀ / 2) * (d.W n : ℝ) ^ (τ₀ / 2) := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    rw [hpow]
    have := mul_le_mul_of_nonneg_left h8
      (mul_nonneg hℓ.le (Real.rpow_nonneg hW0.le (τ₀ / 2)))
    nlinarith
  refine le_trans (measure_mono ?_) (h1n (⟨u n, ⟨hu n, hut n⟩⟩, σ n, p.2))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine lt_of_lt_of_le hω ?_
  by_cases hfar : ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8 ≤ (KLoop.maxDist (d.L n) p.2 : ℝ)
  · have hfar' : ellT (d.L n) (u n) * (d.W n : ℝ) ^ (τ₀ / 2) ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) :=
      hnest.trans hfar
    simp only [hfar, hfar', ↓reduceIte, mul_one]
    have : ‖lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) p.2‖ =
        lkGen (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) p.2 := rfl
    rw [this]
    have := norm_nonneg (gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (u n) ω))
      (spectralZ (E n) (u n)) (loopOf (σ n) p.2))
    unfold loopAbs
    linarith
  · simp only [hfar, ↓reduceIte, mul_zero]
    split_ifs
    · have := norm_nonneg (gloop (d.L n) (d.W n) (blockMat (Sizes.seqHflow d n (u n) ω))
        (spectralZ (E n) (u n)) (loopOf (σ n) p.2))
      unfold loopAbs lkGen
      positivity
    · simp

/-- **A `≺` bound is stable under an eventual pointwise equality** of the dominated quantity. -/
theorem perTimeDomAt_congr_left {U : ℕ → Type*} {ξ ξ' ζ : ∀ n, U n → Sizes.SeqΩ d → ℝ}
    (heq : ∀ᶠ n : ℕ in atTop, ∀ p ω, ξ n p ω = ξ' n p ω)
    (h : PerTimeDomAt (Sizes.seqP d) d.size ξ ζ) : PerTimeDomAt (Sizes.seqP d) d.size ξ' ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, heq] with n hn he p
  have : {ω | ((d.size n : ℕ) : ℝ) ^ τ * ζ n p ω < ξ' n p ω} =
      {ω | ((d.size n : ℕ) : ℝ) ^ τ * ζ n p ω < ξ n p ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, he p ω]
  rw [this]
  exact hn p

/-- **Closure lemma (b), stochastic form: applying a deterministic kernel to a local form and truncating
gives a local form plus `O_≺(W^{-D₀})`.**  Let `X_n(ω)` be the evaluation of the local forms `FX_n`,
`𝔎_n` a kernel with `|𝔎| ≤ N^{a_K}` (`K1`) and decay `δ_n` off the window (`K2'`, `K3'`), `|X| ≤ N^{a_X}`,
and suppose the far part of `X` in `ℓ¹` is `≺ W^{-(D₀ + (k'+a_K+1)/c)}`.  If the deterministic tail
`(1 + N^{k'}) N^k δ N^{a_X}` is `≤ ½ W^{-D₀}`, then `𝒬_u𝔎X - 𝒬_u(𝔎^{tr}X^{tr}) = O_≺(W^{-D₀})`
per time and label, where `𝒬_u(𝔎^{tr}X^{tr})` is the evaluation of the local form `asmF u ρ 𝔎 FX`. -/
theorem kernelAssembly_PT {c D₀ : ℝ} (hc : 0 < c) (hband : Bandwidth d c) (hsize : SizeTendsto d)
    {k k' K : ℕ} [NeZero k] [NeZero k'] {E u ρ δ : ℕ → ℝ} {aK aX : ℕ}
    (𝔎 : ∀ n, (Fin k' → Z2 (d.L n)) → (Fin k → Z2 (d.L n)) → ℂ)
    (FX : ∀ n, LocalForm (d.L n) (d.W n) k K)
    (X : ∀ n, Sizes.SeqΩ d → (Fin k → Z2 (d.L n)) → ℂ)
    (hFX : ∀ n ω c', (FX n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) c' = X n ω c')
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) (hδ0 : ∀ n, 0 ≤ δ n)
    (hK1 : ∀ᶠ n : ℕ in atTop, ∀ a c', ‖𝔎 n a c'‖ ≤ ((d.size n : ℕ) : ℝ) ^ aK)
    (hK2 : ∀ᶠ n : ℕ in atTop, ∀ a c', ρ n ≤ (zdist2 (d.L n) (c' 0 - a 0) : ℝ) →
      (KLoop.maxDist (d.L n) c' : ℝ) < ρ n → ‖𝔎 n a c'‖ ≤ δ n)
    (hK3 : ∀ᶠ n : ℕ in atTop, ∀ a c', ρ n ≤ (KLoop.maxDist (d.L n) a : ℝ) →
      (KLoop.maxDist (d.L n) c' : ℝ) < ρ n → ‖𝔎 n a c'‖ ≤ δ n)
    (hX : ∀ᶠ n : ℕ in atTop, ∀ ω c', ‖X n ω c'‖ ≤ ((d.size n : ℕ) : ℝ) ^ aX)
    (hδ : ∀ᶠ n : ℕ in atTop, (1 + ((d.size n : ℕ) : ℝ) ^ k') *
      (((d.size n : ℕ) : ℝ) ^ k * δ n * ((d.size n : ℕ) : ℝ) ^ aX) ≤ (d.W n : ℝ) ^ (-D₀) / 2)
    (hl1 : PerTimeDomAt (Sizes.seqP d) d.size (U := fun _ => Unit)
      (fun n _ ω => l1far (ρ n) (X n ω))
      (fun n _ _ => (d.W n : ℝ) ^ (-(D₀ + ((k' + aK + 1 : ℕ) : ℝ) / c)))) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k' → Z2 (d.L n)))
      (fun n p ω => ‖Qop (d.L n) (u n) (fun a' => ∑ c', 𝔎 n a' c' * X n ω c') p.2 -
        (asmF (u n) (ρ n) (𝔎 n) (FX n)).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
      (fun n _ _ => (d.W n : ℝ) ^ (-D₀)) := by
  set C : ℝ := ((k' + aK + 1 : ℕ) : ℝ) with hCdef
  have hη0 : ∀ n (p : Unit × (Fin k' → Z2 (d.L n))) (ω : Sizes.SeqΩ d),
      0 ≤ l1far (ρ n) (X n ω) := fun n p ω => l1far_nonneg _ _
  have hη : PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k' → Z2 (d.L n)))
      (fun n p ω => l1far (ρ n) (X n ω)) (fun n _ _ => (d.W n : ℝ) ^ (-(D₀ + C / c))) := by
    intro τ' hτ' D' hD'
    filter_upwards [hl1 τ' hτ' D' hD'] with n hn p
    exact hn ()
  have hD : (D₀ + C / c) - C / c = D₀ := by ring
  have hγ : ∀ᶠ n : ℕ in atTop, (1 + ((d.size n : ℕ) : ℝ) ^ k') *
      (((d.size n : ℕ) : ℝ) ^ k * δ n * ((d.size n : ℕ) : ℝ) ^ aX) ≤
        (d.W n : ℝ) ^ (-((D₀ + C / c) - C / c)) / 2 := by
    rw [hD]; exact hδ
  have hξ : ∀ᶠ n : ℕ in atTop, ∀ (p : Unit × (Fin k' → Z2 (d.L n))) (ω : Sizes.SeqΩ d),
      ‖Qop (d.L n) (u n) (fun a' => ∑ c', 𝔎 n a' c' * X n ω c') p.2 -
        (asmF (u n) (ρ n) (𝔎 n) (FX n)).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖ ≤
      (1 + ((d.size n : ℕ) : ℝ) ^ k') *
        (((d.size n : ℕ) : ℝ) ^ k * δ n * ((d.size n : ℕ) : ℝ) ^ aX) +
        ((d.size n : ℕ) : ℝ) ^ C * l1far (ρ n) (X n ω) := by
    filter_upwards [hK1, hK2, hK3, hX, hsize.eventually_ge_atTop 2] with n h1 h2 h3 hx hN2 p ω
    have hN1 : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by linarith
    have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    have hBK : 0 ≤ ((d.size n : ℕ) : ℝ) ^ aK := by positivity
    have hBX : 0 ≤ ((d.size n : ℕ) : ℝ) ^ aX := by positivity
    have herr := norm_qop_error_le (d.three_le_L n) (hu0 n) (hu1 n) (ρ n) (𝔎 n) (X n ω) hBK hBX
      (hδ0 n) h1 h2 h3 (hx ω) p.2
    rw [eval_asmF (u n) (ρ n) (𝔎 n) (FX n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (X n ω)
      (hFX n ω) p.2]
    refine herr.trans ?_
    have hl := l1far_nonneg (ρ n) (X n ω)
    have hc1 : ((d.L n : ℝ) ^ 2) ^ k ≤ ((d.size n : ℕ) : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (L_sq_le_size d n) k
    have hc2 : ((d.L n : ℝ) ^ 2) ^ k' ≤ ((d.size n : ℕ) : ℝ) ^ k' :=
      pow_le_pow_left₀ (by positivity) (L_sq_le_size d n) k'
    have hNC : ((d.size n : ℕ) : ℝ) ^ C = ((d.size n : ℕ) : ℝ) ^ (k' + aK + 1) := by
      rw [hCdef, Real.rpow_natCast]
    have hcoef : (1 + ((d.L n : ℝ) ^ 2) ^ k') * ((d.size n : ℕ) ^ aK : ℝ) ≤
        ((d.size n : ℕ) : ℝ) ^ C := by
      rw [hNC]
      have h1k : (1 : ℝ) ≤ ((d.size n : ℕ) : ℝ) ^ k' := one_le_pow₀ hN1
      calc (1 + ((d.L n : ℝ) ^ 2) ^ k') * ((d.size n : ℕ) ^ aK : ℝ)
          ≤ (2 * ((d.size n : ℕ) : ℝ) ^ k') * ((d.size n : ℕ) ^ aK : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hBK
            linarith
        _ = 2 * ((d.size n : ℕ) : ℝ) ^ (k' + aK) := by ring
        _ ≤ ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (k' + aK) :=
            mul_le_mul_of_nonneg_right hN2 (by positivity)
        _ = ((d.size n : ℕ) : ℝ) ^ (k' + aK + 1) := by ring
    calc (1 + ((d.L n : ℝ) ^ 2) ^ k') * (((d.L n : ℝ) ^ 2) ^ k * δ n * ((d.size n : ℕ) ^ aX : ℝ) +
          ((d.size n : ℕ) ^ aK : ℝ) * l1far (ρ n) (X n ω))
        = (1 + ((d.L n : ℝ) ^ 2) ^ k') * (((d.L n : ℝ) ^ 2) ^ k * δ n * ((d.size n : ℕ) ^ aX : ℝ)) +
          ((1 + ((d.L n : ℝ) ^ 2) ^ k') * ((d.size n : ℕ) ^ aK : ℝ)) * l1far (ρ n) (X n ω) := by ring
      _ ≤ _ := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_right hcoef hl)
          refine mul_le_mul (by linarith) ?_ (mul_nonneg (mul_nonneg (by positivity) (hδ0 n)) hBX)
            (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 (hδ0 n)) hBX
  have h := errTransport d (C := C) (D := D₀ + C / c) hc (Nat.cast_nonneg _) hband hsize hη0 hη hγ hξ
  simpa only [hD] using h

end Stochastic

section DetSizes

variable {L W : ℕ} [NeZero L] [NeZero W] {k : ℕ} [NeZero k]

/-- The deterministic size of the loop tensor: `|𝓛 - 𝒦| ≤ 2 N^{k+1}` for a Hermitian matrix, from the
crude envelope `norm_gloop_le_crude` and the deterministic `𝒦` bound. -/
theorem norm_lkTensor_le (hW : 1 ≤ W) {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (σ : Fin k → Bool)
    (c : Fin k → Z2 L) {Nr : ℝ} (hη : (etaT E u)⁻¹ ≤ Nr) (hLW : (((L * W) ^ 2 : ℕ) : ℝ) ≤ Nr)
    (hN1 : 1 ≤ Nr) (hK : ‖KLoop.Kcal L W E u (loopOf σ c)‖ ≤ Nr * (etaT E u)⁻¹ ^ k) :
    ‖lkTensor L W E u M σ c‖ ≤ 2 * Nr ^ (k + 1) := by
  have hηpos : 0 < etaT E u := etaT_pos hE hu1
  have hz : etaT E u ≤ |(spectralZ E u).im| := by
    rw [spectralZ_im, abs_of_nonneg]
    · rfl
    · exact hηpos.le
  have hHerm : (blockMat M).IsHermitian := hM.submatrix _
  have hwf : (loopOf σ c).WF := by simp [loopOf, LoopIdx.WF]
  have hg := norm_gloop_le_crude L W hHerm hηpos hz (loopOf σ c) hwf
  have hlen : (loopOf σ c).a.length = k := by simp [loopOf]
  rw [hlen] at hg
  have hW1 : ((W : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have h0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    nlinarith
  have hpow : (etaT E u)⁻¹ ^ k ≤ Nr ^ k := pow_le_pow_left₀ (inv_nonneg.2 hηpos.le) hη k
  have hg2 : ‖gloop L W (blockMat M) (spectralZ E u) (loopOf σ c)‖ ≤ Nr * Nr ^ k := by
    refine hg.trans ?_
    have h1 : (etaT E u)⁻¹ * ((W : ℝ)⁻¹) ^ 2 ≤ (etaT E u)⁻¹ :=
      mul_le_of_le_one_right (inv_nonneg.2 hηpos.le) hW1
    have h2 : ((etaT E u)⁻¹ * ((W : ℝ)⁻¹) ^ 2) ^ k ≤ ((etaT E u)⁻¹) ^ k :=
      pow_le_pow_left₀ (by positivity) h1 k
    calc _ ≤ Nr * ((etaT E u)⁻¹ * ((W : ℝ)⁻¹) ^ 2) ^ k :=
          mul_le_mul_of_nonneg_right hLW (by positivity)
      _ ≤ Nr * Nr ^ k := mul_le_mul_of_nonneg_left (h2.trans hpow) (by linarith)
  have hK2 : ‖KLoop.Kcal L W E u (loopOf σ c)‖ ≤ Nr * Nr ^ k :=
    hK.trans (mul_le_mul_of_nonneg_left hpow (by linarith))
  unfold lkTensor LKf LLf
  refine (norm_sub_le _ _).trans ?_
  calc _ ≤ Nr * Nr ^ k + Nr * Nr ^ k := add_le_add hg2 hK2
    _ = 2 * Nr ^ (k + 1) := by ring

end DetSizes

section FourDet

variable {L W : ℕ} [NeZero L] [NeZero W] {k : ℕ} [NeZero k]

/-- The tail prefactor `P_δ` of the kernel `𝔎` of `ℬ₄` (`K2'`, `K3'`): `|𝔎_{a,c}| ≤ P_δ · dec(ρ/2)` off
the window. -/
def pdelta (L k : ℕ) (u : ℝ) : ℝ :=
  6 * (1 - u)⁻¹ * cL L u + (k : ℝ) * (1 - u)⁻¹ *
    (((L : ℝ) ^ 2) * (3 * cL L u ^ 2 + cL L u) + 2 * cL L u)

/-- `P_δ ≥ 0`. -/
theorem pdelta_nonneg (L k : ℕ) {u : ℝ} (hu1 : u < 1) : 0 ≤ pdelta L k u := by
  have h1u : 0 < 1 - u := by linarith
  have hC := cL_nonneg L u
  unfold pdelta
  positivity

/-- **The kernel `𝔎` of `ℬ₄` satisfies the three hypotheses of the assembly**: `K1` (size),
`K2'` (decay in `|c₀ - a₀|` for `maxDist c < ρ`) and `K3'` (decay in `maxDist a`). -/
theorem kerB4_hyps (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {ρ Nr : ℝ} (hρ : 0 < ρ)
    (hτ : (1 - u)⁻¹ ≤ Nr) :
    (∀ a c : Fin k → Z2 L, ‖kerB4 u a c‖ ≤ 2 * (k : ℝ) * Nr) ∧
    (∀ a c : Fin k → Z2 L, ρ ≤ (zdist2 L (c 0 - a 0) : ℝ) →
        ‖kerB4 u a c‖ ≤ pdelta L k u * dec L u (ρ / 2)) ∧
    (∀ a c : Fin k → Z2 L, ρ ≤ (KLoop.maxDist L a : ℝ) →
        ‖kerB4 u a c‖ ≤ pdelta L k u * dec L u (ρ / 2)) := by
  have hL1 : 1 ≤ L := by omega
  have hℓ : 0 < ellT L u := (ellT_pos_le hL1 hu1).1
  have h1u : 0 < 1 - u := by linarith
  have hτ0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
  have hC := cL_nonneg L u
  have hε := (dec_pos L u (ρ / 2)).le
  refine ⟨fun a c => ?_, fun a c hnear => ?_, fun a c hfar => ?_⟩
  · refine (norm_kerB4_le hL hu0 hu1 a c).trans ?_
    have : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hτ this
  · refine (norm_kerB4_le_near hL hu0 hu1 a c hρ hnear).trans ?_
    have hdec : dec L u ρ ≤ dec L u (ρ / 2) := dec_anti L hℓ (by linarith)
    have h6 : 2 * ((1 - u)⁻¹ * (3 * cL L u * dec L u ρ)) ≤
        6 * (1 - u)⁻¹ * cL L u * dec L u (ρ / 2) := by
      have : 2 * ((1 - u)⁻¹ * (3 * cL L u * dec L u ρ)) = 6 * (1 - u)⁻¹ * cL L u * dec L u ρ := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hdec (by positivity)
    refine h6.trans ?_
    unfold pdelta
    have : 0 ≤ (k : ℝ) * (1 - u)⁻¹ * (((L : ℝ) ^ 2) * (3 * cL L u ^ 2 + cL L u) + 2 * cL L u) := by
      positivity
    nlinarith [mul_nonneg this hε]
  · refine (norm_kerB4_le_far hL hu0 hu1 a c hρ hfar).trans ?_
    unfold pdelta
    have h6 : 0 ≤ 6 * (1 - u)⁻¹ * cL L u := by positivity
    have e : (k : ℝ) * (1 - u)⁻¹ * ((L : ℝ) ^ 2 * (3 * cL L u ^ 2 + cL L u) + 2 * cL L u) =
        (k : ℝ) * (1 - u)⁻¹ * (((L : ℝ) ^ 2) * (3 * cL L u ^ 2 + cL L u) + 2 * cL L u) := rfl
    nlinarith [mul_nonneg h6 hε]

end FourDet

section FourNumerics

variable {L : ℕ} [NeZero L]

/-- `c_L(u) ≤ C₅ N`. -/
theorem cL_le (hL : 3 ≤ L) {u Nr : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hLN : (L : ℝ) ^ 2 ≤ Nr) :
    cL L u ≤ C5 * Nr := by
  have hL1 : 1 ≤ L := by omega
  have h1 : 1 ≤ ellT L u := one_le_ellT hL1 hu0 hu1
  have hinv : (ellT L u ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  have hlog0 : 0 ≤ 1 + Real.log L := by
    have := Real.log_natCast_nonneg L
    linarith
  have hlog : 1 + Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < L)
    linarith
  have hLL : (L : ℝ) ≤ Nr := by
    have h1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    nlinarith
  have hC5 := C5_pos
  unfold cL
  calc C5 * (1 + Real.log L) * (ellT L u ^ 2)⁻¹ ≤ C5 * (1 + Real.log L) * 1 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ C5 * (L : ℝ) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left hlog hC5.le
    _ ≤ C5 * Nr := mul_le_mul_of_nonneg_left hLL hC5.le

/-- The constant `Q_c` bounding `P_δ ≤ Q_c N⁴`. -/
def Qc (k : ℕ) : ℝ := 6 * C5 + (k : ℝ) * (3 * C5 ^ 2 + 3 * C5)

/-- `Q_c > 0`. -/
theorem Qc_pos (k : ℕ) : 0 < Qc k := by
  have := C5_pos
  unfold Qc
  positivity

/-- `P_δ ≤ Q_c N⁴`. -/
theorem pdelta_le (hL : 3 ≤ L) {k : ℕ} {u Nr : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hLN : (L : ℝ) ^ 2 ≤ Nr) (hN1 : 1 ≤ Nr) (hτ : (1 - u)⁻¹ ≤ Nr) :
    pdelta L k u ≤ Qc k * Nr ^ 4 := by
  have hC5 := C5_pos
  have hC0 := cL_nonneg L u
  have hC := cL_le hL hu0 hu1 hLN
  have h1u : 0 < 1 - u := by linarith
  have hτ0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
  have hN0 : 0 ≤ Nr := by linarith
  have hL20 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  set C := cL L u with hCdef
  set τ := (1 - u)⁻¹ with hτdef
  have hτC : τ * C ≤ Nr * (C5 * Nr) := mul_le_mul hτ hC hC0 hN0
  have hC2 : C ^ 2 ≤ (C5 * Nr) ^ 2 := pow_le_pow_left₀ hC0 hC 2
  have h3 : 3 * C ^ 2 + C ≤ 3 * (C5 * Nr) ^ 2 + C5 * Nr := by nlinarith
  have hL3 : (L : ℝ) ^ 2 * (3 * C ^ 2 + C) ≤ Nr * (3 * (C5 * Nr) ^ 2 + C5 * Nr) :=
    mul_le_mul hLN h3 (by positivity) hN0
  have hin : (L : ℝ) ^ 2 * (3 * C ^ 2 + C) + 2 * C ≤
      Nr * (3 * (C5 * Nr) ^ 2 + C5 * Nr) + 2 * (C5 * Nr) := by linarith
  have hin0 : 0 ≤ (L : ℝ) ^ 2 * (3 * C ^ 2 + C) + 2 * C := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkτ : (k : ℝ) * τ * ((L : ℝ) ^ 2 * (3 * C ^ 2 + C) + 2 * C) ≤
      (k : ℝ) * Nr * (Nr * (3 * (C5 * Nr) ^ 2 + C5 * Nr) + 2 * (C5 * Nr)) := by
    have := mul_le_mul hτ hin hin0 hN0
    calc (k : ℝ) * τ * ((L : ℝ) ^ 2 * (3 * C ^ 2 + C) + 2 * C)
        = (k : ℝ) * (τ * ((L : ℝ) ^ 2 * (3 * C ^ 2 + C) + 2 * C)) := by ring
      _ ≤ (k : ℝ) * (Nr * (Nr * (3 * (C5 * Nr) ^ 2 + C5 * Nr) + 2 * (C5 * Nr))) :=
          mul_le_mul_of_nonneg_left this hk0
      _ = _ := by ring
  have hN2 : Nr ^ 2 ≤ Nr ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  have hN3 : Nr ^ 3 ≤ Nr ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  unfold pdelta Qc
  have e1 : 6 * τ * C ≤ 6 * C5 * Nr ^ 4 := by
    have : 6 * τ * C ≤ 6 * (Nr * (C5 * Nr)) := by nlinarith
    nlinarith
  have e2 : (k : ℝ) * Nr * (Nr * (3 * (C5 * Nr) ^ 2 + C5 * Nr) + 2 * (C5 * Nr)) ≤
      (k : ℝ) * (3 * C5 ^ 2 + 3 * C5) * Nr ^ 4 := by
    have : (k : ℝ) * Nr * (Nr * (3 * (C5 * Nr) ^ 2 + C5 * Nr) + 2 * (C5 * Nr)) =
        (k : ℝ) * (3 * C5 ^ 2 * Nr ^ 4 + C5 * Nr ^ 3 + 2 * C5 * Nr ^ 2) := by ring
    rw [this]
    have : 3 * C5 ^ 2 * Nr ^ 4 + C5 * Nr ^ 3 + 2 * C5 * Nr ^ 2 ≤ (3 * C5 ^ 2 + 3 * C5) * Nr ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_left hN3 hC5.le, mul_le_mul_of_nonneg_left hN2 hC5.le]
    calc (k : ℝ) * (3 * C5 ^ 2 * Nr ^ 4 + C5 * Nr ^ 3 + 2 * C5 * Nr ^ 2)
        ≤ (k : ℝ) * ((3 * C5 ^ 2 + 3 * C5) * Nr ^ 4) := mul_le_mul_of_nonneg_left this hk0
      _ = _ := by ring
  calc 6 * τ * C + (k : ℝ) * τ * ((L : ℝ) ^ 2 * (3 * C ^ 2 + C) + 2 * C)
      ≤ 6 * C5 * Nr ^ 4 + (k : ℝ) * (3 * C5 ^ 2 + 3 * C5) * Nr ^ 4 := add_le_add e1 (hkτ.trans e2)
    _ = (6 * C5 + (k : ℝ) * (3 * C5 ^ 2 + 3 * C5)) * Nr ^ 4 := by ring

end FourNumerics

section FourPackage

variable {L W : ℕ} [NeZero L] [NeZero W] {k : ℕ} [NeZero k]

/-- `|(Z_L²)^k| ≤ N^k`. -/
theorem card_le_pow {Nr : ℝ} (hLN : (L : ℝ) ^ 2 ≤ Nr) : ((L : ℝ) ^ 2) ^ k ≤ Nr ^ k :=
  pow_le_pow_left₀ (by positivity) hLN k

/-- `1 + |(Z_L²)^k| ≤ 2 N^k`. -/
theorem one_add_card_le {Nr : ℝ} (hN1 : 1 ≤ Nr) (hLN : (L : ℝ) ^ 2 ≤ Nr) :
    1 + ((L : ℝ) ^ 2) ^ k ≤ 2 * Nr ^ k := by
  have h1 : (1 : ℝ) ≤ Nr ^ k := one_le_pow₀ hN1
  have := card_le_pow (k := k) hLN
  linarith

/-- **`C1`: the coefficient bound of the assembled form for `ℬ₄`**: `≤ N^{3k+3}`. -/
theorem four_coef (hL : 3 ≤ L) (hW : 1 ≤ W) {E u Nr : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ρ : ℝ)
    (σ : Fin k → Bool) (hN1 : 1 ≤ Nr) (hLN : (L : ℝ) ^ 2 ≤ Nr) (hτ : (1 - u)⁻¹ ≤ Nr)
    (hη : (etaT E u)⁻¹ ≤ Nr) (hηpos : 0 < etaT E u)
    (hKc : ∀ b : Fin k → Z2 L, ‖KLoop.Kcal L W E u (loopOf σ b)‖ ≤ Nr * (etaT E u)⁻¹ ^ k)
    (hc1 : 8 * (k : ℝ) ≤ Nr) (a : Fin k → Z2 L) (j : Fin (k + 1)) (q : Fin j → Mono L W) :
    ‖(asmF u ρ (kerB4 u) (lkF σ E u : LocalForm L W k k)).coef a j q‖ ≤ Nr ^ (3 * k + 3) := by
  have hN0 : 0 < Nr := by linarith
  have hpow : (etaT E u)⁻¹ ^ k ≤ Nr ^ k := pow_le_pow_left₀ (inv_nonneg.2 hηpos.le) hη k
  have hKb : ∀ b : Fin k → Z2 L, ‖KLoop.Kcal L W E u (loopOf σ b)‖ ≤ Nr ^ (k + 1) := fun b =>
    (hKc b).trans (by
      calc Nr * (etaT E u)⁻¹ ^ k ≤ Nr * Nr ^ k := mul_le_mul_of_nonneg_left hpow hN0.le
        _ = Nr ^ (k + 1) := by ring)
  have hN1k : (1 : ℝ) ≤ Nr ^ (k + 1) := one_le_pow₀ hN1
  have hlk := coef_lkF_le hW σ E u (B := Nr ^ (k + 1)) (by positivity) hKb
  have hK1 := (kerB4_hyps (k := k) hL hu0 hu1 (ρ := 1) one_pos hτ).1
  have hBK : (0 : ℝ) ≤ 2 * (k : ℝ) * Nr := by positivity
  have h := coef_asmF_le hL hu0 hu1 ρ (kerB4 u) (lkF σ E u : LocalForm L W k k)
    (B := 1 + Nr ^ (k + 1)) (B_K := 2 * (k : ℝ) * Nr) (by positivity) hBK hlk hK1 a j q
  refine h.trans ?_
  have hc := card_le_pow (L := L) (k := k) hLN
  have h2 := one_add_card_le (L := L) (k := k) hN1 hLN
  have h3 : 1 + Nr ^ (k + 1) ≤ 2 * Nr ^ (k + 1) := by linarith
  calc (1 + ((L : ℝ) ^ 2) ^ k) * (((L : ℝ) ^ 2) ^ k * (2 * (k : ℝ) * Nr) * (1 + Nr ^ (k + 1)))
      ≤ (2 * Nr ^ k) * (Nr ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1))) := by
        gcongr
    _ = (8 * (k : ℝ)) * Nr ^ (3 * k + 2) := by ring
    _ ≤ Nr * Nr ^ (3 * k + 2) := mul_le_mul_of_nonneg_right hc1 (by positivity)
    _ = Nr ^ (3 * k + 3) := by ring

/-- **`C2`: locality of the assembled form for `ℬ₄`**: `Loc0 (4ρ)`. -/
theorem four_loc (u ρ : ℝ) (σ : Fin k → Bool) (E : ℝ) :
    Loc0 (4 * ρ) (asmF u ρ (kerB4 u) (lkF σ E u : LocalForm L W k k)) := by
  have h := loc0_asmF u ρ (kerB4 u) (lkF σ E u : LocalForm L W k k)
    (loc0_trunc_lkF (L := L) (W := W) σ E u ρ)
  have e : 2 * ρ + 2 * ρ = 4 * ρ := by ring
  rwa [e] at h

/-- **`C4`: far labels of the assembled form for `ℬ₄` are deterministically tiny**: for a Hermitian `M`
and `maxDist b ≥ ρ`, `|F_b| ≤ N^{3k+6} dec(ρ/2)`. -/
theorem four_far (hL : 3 ≤ L) (hW : 1 ≤ W) {E u Nr ρ Tgt : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (hρ : 0 < ρ) (σ : Fin k → Bool) (hN1 : 1 ≤ Nr) (hLN : (L : ℝ) ^ 2 ≤ Nr)
    (hNLW : (((L * W) ^ 2 : ℕ) : ℝ) ≤ Nr) (hτ : (1 - u)⁻¹ ≤ Nr) (hη : (etaT E u)⁻¹ ≤ Nr)
    (hKc : ∀ b : Fin k → Z2 L, ‖KLoop.Kcal L W E u (loopOf σ b)‖ ≤ Nr * (etaT E u)⁻¹ ^ k)
    (hc3 : 4 * (k : ℝ) * C5 ≤ Nr) (htail : Nr ^ (3 * k + 6) * dec L u (ρ / 2) ≤ Tgt)
    {M : Matrix (Idx L W) (Idx L W) ℂ} (hM : M.IsHermitian) (b : Fin k → Z2 L)
    (hb : ρ ≤ (KLoop.maxDist L b : ℝ)) :
    ‖(asmF u ρ (kerB4 u) (lkF σ E u : LocalForm L W k k)).eval E u M b‖ ≤ Tgt := by
  have hN0 : 0 < Nr := by linarith
  have hηpos : 0 < etaT E u := etaT_pos hE hu1
  have hA : ∀ c, ‖lkTensor L W E u M σ c‖ ≤ 2 * Nr ^ (k + 1) := fun c =>
    norm_lkTensor_le hW hE hu1 hM σ c hη hNLW hN1 (hKc c)
  obtain ⟨hK1, -, -⟩ := kerB4_hyps (k := k) hL hu0 hu1 hρ hτ
  have hBK : (0 : ℝ) ≤ 2 * (k : ℝ) * Nr := by positivity
  have h := norm_eval_asmF_le_far hL hu0 hu1 ρ (kerB4 u) (lkF σ E u : LocalForm L W k k) E u M
    (lkTensor L W E u M σ) (fun c => eval_lkF σ E u M c) (B_K := 2 * (k : ℝ) * Nr)
    (B_X := 2 * Nr ^ (k + 1)) hBK (by positivity) hK1 hA b hb
  refine h.trans ?_
  obtain ⟨j₀, hj₀S, hj⟩ := exists_far hρ hb
  have hj0 : j₀ ≠ 0 := (Finset.mem_erase.mp hj₀S).1
  have hϑ := norm_vartheta_le_decay hL hu0 hu1 b hj0 (r := ρ / 2) hj
  have hcL := cL_le hL hu0 hu1 hLN
  have hε := (dec_pos L u (ρ / 2)).le
  have hC0 := cL_nonneg L u
  have hϑ2 : ‖vartheta L u b‖ ≤ C5 * Nr * dec L u (ρ / 2) :=
    hϑ.trans (mul_le_mul_of_nonneg_right hcL hε)
  have hc := card_le_pow (L := L) (k := k) hLN
  have hpref : ((L : ℝ) ^ 2) ^ k * (((L : ℝ) ^ 2) ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1))) ≤
      Nr ^ k * (Nr ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1))) := by gcongr
  have hC5 := C5_pos
  calc (((L : ℝ) ^ 2) ^ k * (((L : ℝ) ^ 2) ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1)))) *
        ‖vartheta L u b‖
      ≤ (Nr ^ k * (Nr ^ k * (2 * (k : ℝ) * Nr) * (2 * Nr ^ (k + 1)))) * (C5 * Nr * dec L u (ρ / 2)) :=
        mul_le_mul hpref hϑ2 (norm_nonneg _) (by positivity)
    _ = (4 * (k : ℝ) * C5) * Nr ^ (3 * k + 3) * dec L u (ρ / 2) := by ring
    _ ≤ Nr * Nr ^ (3 * k + 3) * dec L u (ρ / 2) := by
        gcongr
    _ = Nr ^ (3 * k + 4) * dec L u (ρ / 2) := by ring
    _ ≤ Nr ^ (3 * k + 6) * dec L u (ρ / 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 (by omega)) hε
    _ ≤ Tgt := htail

/-- **`C5`: the deterministic tail of the error for `ℬ₄` is at most half the target**:
`(1 + N^k)(N^k P_δ dec(ρ/2) N^{k+2}) ≤ Tgt/2` if `N^{3k+7} dec(ρ/2) ≤ Tgt` and `8 Q_c ≤ N`. -/
theorem four_tail (hL : 3 ≤ L) {u Nr ρ Tgt : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hN1 : 1 ≤ Nr)
    (hLN : (L : ℝ) ^ 2 ≤ Nr) (hτ : (1 - u)⁻¹ ≤ Nr) (hc2 : 8 * Qc k ≤ Nr)
    (htail : Nr ^ (3 * k + 7) * dec L u (ρ / 2) ≤ Tgt) :
    (1 + Nr ^ k) * (Nr ^ k * (pdelta L k u * dec L u (ρ / 2)) * Nr ^ (k + 2)) ≤ Tgt / 2 := by
  have hN0 : 0 < Nr := by linarith
  have hε := (dec_pos L u (ρ / 2)).le
  have hp := pdelta_le (k := k) hL hu0 hu1 hLN hN1 hτ
  have hp0 := pdelta_nonneg L k hu1
  have hQ := Qc_pos k
  have h1k : (1 : ℝ) ≤ Nr ^ k := one_le_pow₀ hN1
  calc (1 + Nr ^ k) * (Nr ^ k * (pdelta L k u * dec L u (ρ / 2)) * Nr ^ (k + 2))
      ≤ (2 * Nr ^ k) * (Nr ^ k * ((Qc k * Nr ^ 4) * dec L u (ρ / 2)) * Nr ^ (k + 2)) := by
        gcongr
        linarith
    _ = (2 * Qc k) * Nr ^ (3 * k + 6) * dec L u (ρ / 2) := by ring
    _ ≤ (Nr / 4) * Nr ^ (3 * k + 6) * dec L u (ρ / 2) := by
        gcongr
        linarith
    _ = Nr ^ (3 * k + 7) * dec L u (ρ / 2) / 4 := by ring
    _ ≤ Tgt / 2 := by
        have hX0 : 0 ≤ Nr ^ (3 * k + 7) * dec L u (ρ / 2) := by positivity
        linarith

end FourPackage

section EtaFacts

/-- `((1-u) Im m)^{-1} ≤ N` from `N^{-1+τ} ≤ 1-u`, `μ ≤ Im m`, `1 ≤ μ N^τ`. -/
theorem eta_inv {N x μ m τ : ℝ} (hN : 0 < N) (hx : N ^ (-1 + τ) ≤ x)
    (hμ : 0 < μ) (hm : μ ≤ m) (hμN : 1 ≤ μ * N ^ τ) : (x * m)⁻¹ ≤ N := by
  have e : N * N ^ (-1 + τ) = N ^ τ := by
    rw [Real.rpow_add hN, Real.rpow_neg_one]; field_simp
  have hp : 0 < N ^ (-1 + τ) := Real.rpow_pos_of_pos hN _
  have hx0 : 0 < x := lt_of_lt_of_le hp hx
  have hxm : 0 < x * m := mul_pos hx0 (lt_of_lt_of_le hμ hm)
  have key : 1 ≤ N * (x * m) := by
    rw [← e] at hμN
    have : μ * (N * N ^ (-1 + τ)) ≤ m * (N * x) :=
      mul_le_mul hm (mul_le_mul_of_nonneg_left hx hN.le) (by positivity) (by linarith)
    nlinarith
  calc (x * m)⁻¹ = (x * m)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (x * m)⁻¹ * (N * (x * m)) := mul_le_mul_of_nonneg_left key (inv_nonneg.2 hxm.le)
    _ = N := by rw [mul_comm N, ← mul_assoc, inv_mul_cancel₀ hxm.ne', one_mul]

/-- `(1-u)⁻¹ ≤ N` from `N^{-1+τ} ≤ 1-u`, `τ > 0`, `N ≥ 1`. -/
theorem inv_one_sub_le {N x τ : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ) (hx : N ^ (-1 + τ) ≤ x) : x⁻¹ ≤ N := by
  have hN0 : 0 < N := by linarith
  have hp : 0 < N ^ (-1 + τ) := Real.rpow_pos_of_pos hN0 _
  have h1 : x⁻¹ ≤ (N ^ (-1 + τ))⁻¹ := inv_anti₀ hp hx
  have h2 : (N ^ (-1 + τ))⁻¹ = N ^ (1 - τ) := by
    rw [← Real.rpow_neg hN0.le]; congr 1; ring
  have h3 : N ^ (1 - τ) ≤ N ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  rw [Real.rpow_one] at h3
  linarith

/-- Uniform bounds on `Im m^{(E n)}` for `|E n| ≤ 2 - κ`. -/
theorem im_bounds {κ : ℝ} {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ n, μ ≤ (spectralM (E n)).im := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  refine ⟨Real.sqrt (4 - (2 - κ) ^ 2) / 2, ?_, fun n => ?_⟩
  · have : 0 < 4 - (2 - κ) ^ 2 := by nlinarith
    positivity
  · rw [spectralM_im]
    have h1 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (E n)) (hE n) 2
      rwa [sq_abs] at this
    have := Real.sqrt_le_sqrt (show 4 - (2 - κ) ^ 2 ≤ 4 - E n ^ 2 by linarith)
    linarith

/-- `dec(ρ/2) = exp(-W^{τ₀}/320000)` for `ρ = ℓ_u W^{τ₀}/8`. -/
theorem dec_rho {L : ℕ} [NeZero L] {u W τ₀ : ℝ} (hℓ : 0 < ellT L u) :
    dec L u (ellT L u * W ^ τ₀ / 8 / 2) = Real.exp (-(W ^ τ₀ / 320000)) := by
  unfold dec
  congr 1
  field_simp
  ring

end EtaFacts

section Closure

variable {L W : ℕ} [NeZero L] [NeZero W] {k k' K : ℕ} [NeZero k] [NeZero k']

/-! ### Cut contraction (closure lemma (e)) -/

/-- The cut kernel: contract the last two labels `(a, b)` of a `(k+2)`-tensor against `S(a,b)`,
`(Σ_z cutKer S c z Z_z) = Σ_{a,b} S(a,b) Z(c,a,b)` (the cut sums `Σ_{a,b} 𝓛 S 𝓛` of `B₁–B₃`). -/
def cutKer (S : Z2 L → Z2 L → ℂ) (c : Fin k → Z2 L) (z : Fin (k + 2) → Z2 L) : ℂ :=
  if (∀ i : Fin k, z (Fin.castAdd 2 i) = c i) then S (z (Fin.natAdd k 0)) (z (Fin.natAdd k 1)) else 0

/-- **Closure lemma (e), the cut sum**: `Σ_z cutKer_{c,z} Z_z = Σ_{a,b} S(a,b) Z(c,a,b)`. -/
theorem sum_cutKer (S : Z2 L → Z2 L → ℂ) (Z : (Fin (k + 2) → Z2 L) → ℂ) (c : Fin k → Z2 L) :
    ∑ z, cutKer S c z * Z z = ∑ a, ∑ b, S a b * Z (Fin.append c ![a, b]) := by
  rw [← (Fin.appendEquiv k 2).sum_comp, Fintype.sum_prod_type]
  have h : ∀ c' : Fin k → Z2 L, ∀ w : Fin 2 → Z2 L,
      cutKer S c ((Fin.appendEquiv k 2) (c', w)) * Z ((Fin.appendEquiv k 2) (c', w)) =
        if c' = c then S (w 0) (w 1) * Z (Fin.append c' w) else 0 := by
    intro c' w
    have hz : (Fin.appendEquiv k 2) (c', w) = Fin.append c' w := rfl
    rw [hz]
    unfold cutKer
    simp only [Fin.append_left, Fin.append_right]
    by_cases hc : c' = c
    · subst hc; simp
    · have : ¬ ∀ i : Fin k, c' i = c i := fun h => hc (funext h)
      simp [this, hc]
  simp_rw [h]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (piFinTwoEquiv (fun _ : Fin 2 => Z2 L)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : ((piFinTwoEquiv (fun _ : Fin 2 => Z2 L)).symm (a, b)) = ![a, b] := by
    funext i; fin_cases i <;> rfl
  rw [this]
  rfl

/-- `castAdd 2 0 = 0`. -/
theorem castAdd_zero' (k : ℕ) [NeZero k] : (Fin.castAdd 2 (0 : Fin k) : Fin (k + 2)) = 0 :=
  Fin.ext (by simp)

/-- The hypotheses of the assembly for the cut kernel (source `(k+2)` labels, target `k` labels):
`K1` `|S| ≤ B_S`; `K2'`, `K3'` hold with `δ = 0` (the kernel forces `z|_k = a`, so `z₀ = a₀` and
`maxDist a ≤ maxDist z`). -/
theorem cutKer_hyps (S : Z2 L → Z2 L → ℂ) {B_S ρ : ℝ} (hS : ∀ a b, ‖S a b‖ ≤ B_S) (hBS : 0 ≤ B_S)
    (hρ : 0 < ρ) :
    (∀ (a : Fin k → Z2 L) (z : Fin (k + 2) → Z2 L), ‖cutKer S a z‖ ≤ B_S) ∧
    (∀ (a : Fin k → Z2 L) (z : Fin (k + 2) → Z2 L), ρ ≤ (zdist2 L (z 0 - a 0) : ℝ) →
      (KLoop.maxDist L z : ℝ) < ρ → ‖cutKer S a z‖ ≤ 0) ∧
    (∀ (a : Fin k → Z2 L) (z : Fin (k + 2) → Z2 L), ρ ≤ (KLoop.maxDist L a : ℝ) →
      (KLoop.maxDist L z : ℝ) < ρ → ‖cutKer S a z‖ ≤ 0) := by
  refine ⟨fun a z => ?_, fun a z hnear _ => ?_, fun a z hfar hz => ?_⟩
  · unfold cutKer
    split_ifs
    · exact hS _ _
    · simpa using hBS
  · have hne : ¬ ∀ i : Fin k, z (Fin.castAdd 2 i) = a i := by
      intro h
      have h0 := h 0
      rw [castAdd_zero'] at h0
      rw [h0, sub_self, zdist2_zero] at hnear
      simp at hnear
      linarith
    simp [cutKer, hne]
  · have hne : ¬ ∀ i : Fin k, z (Fin.castAdd 2 i) = a i := by
      intro h
      have hle : (KLoop.maxDist L a : ℝ) ≤ (KLoop.maxDist L z : ℝ) := by
        have : KLoop.maxDist L a ≤ KLoop.maxDist L z := by
          unfold KLoop.maxDist
          refine Finset.sup_le fun p _ => ?_
          rw [← h p.1, ← h p.2]
          exact zdist2_le_maxDist z (Fin.castAdd 2 p.1) (Fin.castAdd 2 p.2)
        exact_mod_cast this
      linarith
    simp [cutKer, hne]

end Closure

section VarthetaDot

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

open scoped Matrix.Norms.Operator in
/-- The row `ℓ¹` sums of `Θ_u S` are at most `(1-u)⁻¹`. -/
theorem sum_norm_ThetaSB_row_le (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x : Z2 L) :
    ∑ e : Z2 L, ‖(Theta L (u : ℂ) * SB L) x e‖ ≤ (1 - u)⁻¹ := by
  refine (sum_norm_row_le_opNorm _ x).trans ?_
  calc ‖Theta L (u : ℂ) * SB L‖ ≤ ‖Theta L (u : ℂ)‖ * ‖SB L‖ := norm_mul_le _ _
    _ = ‖Theta L (u : ℂ)‖ := by rw [norm_SB L hL, mul_one]
    _ ≤ (1 - ‖(u : ℂ)‖)⁻¹ := norm_Theta_le L hL (norm_ofReal_lt_one hu0 hu1)
    _ = (1 - u)⁻¹ := by rw [Complex.norm_real, Real.norm_of_nonneg hu0]

/-- `(1-u)²|(Θ_u S Θ_u)(x,y)| ≤ 1`. -/
theorem sq_mul_norm_ThetaSBTheta_le_one (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (x y : Z2 L) :
    (1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖ ≤ 1 := by
  have h1u : 0 < 1 - u := by linarith
  have hτ : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
  have hrow := sum_norm_ThetaSB_row_le hL hu0 hu1 x
  have hΘ : ∀ e : Z2 L, ‖Theta L (u : ℂ) e y‖ ≤ (1 - u)⁻¹ := fun e =>
    (Finset.single_le_sum (f := fun y => ‖Theta L (u : ℂ) e y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ y)).trans (sum_norm_theta_row_le hL hu0 hu1 e)
  calc (1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖
      = (1 - u) ^ 2 * ‖∑ e : Z2 L, (Theta L (u : ℂ) * SB L) x e * Theta L (u : ℂ) e y‖ := by
        rw [Matrix.mul_apply]
    _ ≤ (1 - u) ^ 2 * ∑ e : Z2 L, ‖(Theta L (u : ℂ) * SB L) x e‖ * (1 - u)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        refine Finset.sum_le_sum fun e _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hΘ e) (norm_nonneg _)
    _ = (1 - u) ^ 2 * ((∑ e : Z2 L, ‖(Theta L (u : ℂ) * SB L) x e‖) * (1 - u)⁻¹) := by
        rw [Finset.sum_mul]
    _ ≤ (1 - u) ^ 2 * ((1 - u)⁻¹ * (1 - u)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hrow hτ
    _ = 1 := by field_simp

/-- `(1-u)²|(Θ_u S Θ_u)(x,y)| ≤ 3 |Z_L²| c_L² dec(|x-y|)`. -/
theorem sq_mul_norm_ThetaSBTheta_le_decay (hL : 3 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (x y : Z2 L) :
    (1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖ ≤
      3 * (L : ℝ) ^ 2 * cL L u ^ 2 * dec L u (zdist2 L (x - y) : ℝ) := by
  have hL1 : 1 ≤ L := by omega
  have h1u : 0 < 1 - u := by linarith
  have hℓ : 0 < ellT L u := (ellT_pos_le hL1 hu1).1
  have hC := cL_nonneg L u
  rw [Matrix.mul_assoc, ← thetaGenMat_one_eq, Matrix.mul_apply]
  have hterm : ∀ z : Z2 L, (1 - u) ^ 2 * ‖Theta L (u : ℂ) x z * thetaGenMat L 1 u z y‖ ≤
      3 * cL L u ^ 2 * dec L u (zdist2 L (x - y) : ℝ) := by
    intro z
    have h1 := theta_decay hL hu0 hu1 x z
    have h2 := T_decay hL hu0 hu1 z y
    have htri := zdist2_sub_le L x z y
    have hd : (zdist2 L (x - y) : ℝ) ≤ (zdist2 L (x - z) : ℝ) + (zdist2 L (z - y) : ℝ) := by
      exact_mod_cast htri
    have hdec : dec L u ((zdist2 L (x - z) : ℝ) + (zdist2 L (z - y) : ℝ)) ≤
        dec L u (zdist2 L (x - y) : ℝ) := dec_anti L hℓ hd
    rw [norm_mul]
    calc (1 - u) ^ 2 * (‖Theta L (u : ℂ) x z‖ * ‖thetaGenMat L 1 u z y‖)
        = ((1 - u) * ‖Theta L (u : ℂ) x z‖) * ((1 - u) * ‖thetaGenMat L 1 u z y‖) := by ring
      _ ≤ (cL L u * dec L u (zdist2 L (x - z) : ℝ)) *
            (3 * cL L u * dec L u (zdist2 L (z - y) : ℝ)) :=
          mul_le_mul h1 h2 (mul_nonneg h1u.le (norm_nonneg _)) (mul_nonneg hC (dec_pos L u _).le)
      _ = 3 * cL L u ^ 2 * dec L u ((zdist2 L (x - z) : ℝ) + (zdist2 L (z - y) : ℝ)) := by
          rw [dec_add]; ring
      _ ≤ 3 * cL L u ^ 2 * dec L u (zdist2 L (x - y) : ℝ) :=
          mul_le_mul_of_nonneg_left hdec (by positivity)
  calc (1 - u) ^ 2 * ‖∑ z : Z2 L, Theta L (u : ℂ) x z * thetaGenMat L 1 u z y‖
      ≤ (1 - u) ^ 2 * ∑ z : Z2 L, ‖Theta L (u : ℂ) x z * thetaGenMat L 1 u z y‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ z : Z2 L, (1 - u) ^ 2 * ‖Theta L (u : ℂ) x z * thetaGenMat L 1 u z y‖ := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _z : Z2 L, 3 * cL L u ^ 2 * dec L u (zdist2 L (x - y) : ℝ) :=
        Finset.sum_le_sum fun z _ => hterm z
    _ = 3 * (L : ℝ) ^ 2 * cL L u ^ 2 * dec L u (zdist2 L (x - y) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : (Fintype.card (Z2 L) : ℝ) = (L : ℝ) ^ 2 := by simp [Z2, ZMod.card]; ring
        rw [this]; ring

/-- The closed form of `ϑ̇_u` (`QopAlgebra` (v)). -/
theorem varthetaDot_eq (hL : 3 ≤ L) (hk : 2 ≤ k) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (a : Fin k → Z2 L) :
    varthetaDot L u a =
      -((k - 1 : ℕ) : ℂ) * ((1 - u : ℝ) : ℂ) ^ (k - 2) *
          ∏ i ∈ Finset.univ.erase (0 : Fin k), Theta L (u : ℂ) (a 0) (a i) +
        ((1 - u : ℝ) : ℂ) ^ (k - 1) * ∑ j ∈ Finset.univ.erase (0 : Fin k),
          (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j) *
            ∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j, Theta L (u : ℂ) (a 0) (a i) :=
  (qopAlgebra L hL k hk u hu0 hu1).2.2.2.2.1 a

/-- The structural bound (★): `|ϑ̇_{u,a}| ≤ (k-1)(1-u)⁻¹ ∏_{i≠0} w_i + (1-u)⁻¹ Σ_{j≠0} A_j ∏_{i≠0,j} w_i`,
`w_i = (1-u)|Θ_u(a₀,a_i)|`, `A_j = (1-u)²|(ΘSΘ)(a₀,a_j)|`. -/
theorem norm_varthetaDot_le_star (hL : 3 ≤ L) (hk : 2 ≤ k) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (a : Fin k → Z2 L) :
    ‖varthetaDot L u a‖ ≤
      ((k : ℝ) - 1) * (1 - u)⁻¹ *
          ∏ i ∈ Finset.univ.erase (0 : Fin k), ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖) +
        (1 - u)⁻¹ * ∑ j ∈ Finset.univ.erase (0 : Fin k),
          ((1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j)‖) *
            ∏ i ∈ (Finset.univ.erase (0 : Fin k)).erase j,
              ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖) := by
  have h1u : 0 < 1 - u := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  set S0 : Finset (Fin (m + 2)) := Finset.univ.erase (0 : Fin (m + 2)) with hS0
  have hcard : S0.card = m + 1 := by
    rw [hS0, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  rw [varthetaDot_eq hL hk hu0 hu1]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- first term
    rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_prod, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg h1u.le, Finset.prod_mul_distrib, Finset.prod_const, hcard]
    have hk1 : (((m + 2 - 1 : ℕ) : ℝ)) = ((m + 2 : ℕ) : ℝ) - 1 := by
      have : (m + 2 - 1 : ℕ) = m + 1 := by omega
      rw [this]; push_cast; ring
    rw [hk1]
    have e : (m + 2 - 2 : ℕ) = m := by omega
    rw [e]
    apply le_of_eq
    field_simp
    ring
  · -- second term
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg h1u.le]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hcardj : (S0.erase j).card = m := by
      rw [Finset.card_erase_of_mem hj, hcard]; simp
    rw [norm_mul, norm_prod, Finset.prod_mul_distrib, Finset.prod_const, hcardj]
    apply le_of_eq
    have e : (m + 2 - 1 : ℕ) = m + 1 := by omega
    rw [e]
    field_simp
    ring

/-- **`K1` for `ϑ̇`**: `|ϑ̇_{u,a}| ≤ 2(k-1)(1-u)⁻¹`. -/
theorem norm_varthetaDot_le (hL : 3 ≤ L) (hk : 2 ≤ k) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (a : Fin k → Z2 L) : ‖varthetaDot L u a‖ ≤ 2 * ((k : ℝ) - 1) * (1 - u)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  have hτ : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
  refine (norm_varthetaDot_le_star hL hk hu0 hu1 a).trans ?_
  set S0 : Finset (Fin k) := Finset.univ.erase (0 : Fin k) with hS0
  have hcard : (S0.card : ℝ) = (k : ℝ) - 1 := by
    rw [hS0, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (NeZero.pos k)]; simp
  have hw : ∀ i, (1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖ ≤ 1 := fun i =>
    one_sub_mul_norm_theta_le_one hL hu0 hu1 _ _
  have hw0 : ∀ i, 0 ≤ (1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖ := fun i =>
    mul_nonneg h1u.le (norm_nonneg _)
  have hP : ∏ i ∈ S0, ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => hw0 i) (fun i _ => hw i)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast NeZero.pos k
    linarith
  have hT2 : ∑ j ∈ S0, ((1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j)‖) *
      ∏ i ∈ S0.erase j, ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖) ≤ ((k : ℝ) - 1) := by
    calc _ ≤ ∑ _j ∈ S0, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
          have hA := sq_mul_norm_ThetaSBTheta_le_one hL hu0 hu1 (a 0) (a j)
          have hQ : ∏ i ∈ S0.erase j, ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖) ≤ 1 :=
            Finset.prod_le_one₀ (fun i _ => hw0 i) (fun i _ => hw i)
          calc _ ≤ 1 * 1 := mul_le_mul hA hQ (Finset.prod_nonneg fun i _ => hw0 i) zero_le_one
            _ = 1 := one_mul 1
      _ = ((k : ℝ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  calc ((k : ℝ) - 1) * (1 - u)⁻¹ *
          ∏ i ∈ S0, ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖) +
        (1 - u)⁻¹ * ∑ j ∈ S0, ((1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j)‖) *
            ∏ i ∈ S0.erase j, ((1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖)
      ≤ ((k : ℝ) - 1) * (1 - u)⁻¹ * 1 + (1 - u)⁻¹ * ((k : ℝ) - 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hP (mul_nonneg hk1 hτ))
          (mul_le_mul_of_nonneg_left hT2 hτ)
    _ = 2 * ((k : ℝ) - 1) * (1 - u)⁻¹ := by ring

/-- **`K3` for `ϑ̇`** (decay of `ϑ̇_{u,a}` in `maxDist a`, `QopAlgebra` (v) and property 5): if
`maxDist a ≥ r > 0`, then `|ϑ̇_{u,a}| ≤ (k-1)(1-u)⁻¹(2c_L + 3|Z_L²| c_L²) dec(r/2)`. -/
theorem norm_varthetaDot_le_decay (hL : 3 ≤ L) (hk : 2 ≤ k) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (a : Fin k → Z2 L) {r : ℝ} (hr : 0 < r) (hfar : r ≤ (KLoop.maxDist L a : ℝ)) :
    ‖varthetaDot L u a‖ ≤
      ((k : ℝ) - 1) * (1 - u)⁻¹ * (2 * cL L u + 3 * (L : ℝ) ^ 2 * cL L u ^ 2) * dec L u (r / 2) := by
  have hL1 : 1 ≤ L := by omega
  have h1u : 0 < 1 - u := by linarith
  have hτ : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
  have hℓ : 0 < ellT L u := (ellT_pos_le hL1 hu1).1
  have hC := cL_nonneg L u
  have hε := (dec_pos L u (r / 2)).le
  obtain ⟨j₀, hj₀S, hj⟩ := exists_far hr hfar
  refine (norm_varthetaDot_le_star hL hk hu0 hu1 a).trans ?_
  set S0 : Finset (Fin k) := Finset.univ.erase (0 : Fin k) with hS0
  have hcard : (S0.card : ℝ) = (k : ℝ) - 1 := by
    rw [hS0, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (NeZero.pos k)]; simp
  set w : Fin k → ℝ := fun i => (1 - u) * ‖Theta L (u : ℂ) (a 0) (a i)‖ with hwdef
  have hw : ∀ i, w i ≤ 1 := fun i => one_sub_mul_norm_theta_le_one hL hu0 hu1 _ _
  have hw0 : ∀ i, 0 ≤ w i := fun i => mul_nonneg h1u.le (norm_nonneg _)
  have hwj₀ : w j₀ ≤ cL L u * dec L u (r / 2) :=
    (theta_decay hL hu0 hu1 (a 0) (a j₀)).trans
      (mul_le_mul_of_nonneg_left (dec_anti L hℓ hj) hC)
  have hslot : ∀ T : Finset (Fin k), j₀ ∈ T → ∏ i ∈ T, w i ≤ w j₀ := by
    intro T hjT
    rw [← Finset.mul_prod_erase T w hjT]
    have : ∏ i ∈ T.erase j₀, w i ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => hw0 i) (fun i _ => hw i)
    calc w j₀ * ∏ i ∈ T.erase j₀, w i ≤ w j₀ * 1 := mul_le_mul_of_nonneg_left this (hw0 j₀)
      _ = w j₀ := mul_one _
  have hP : ∏ i ∈ S0, w i ≤ cL L u * dec L u (r / 2) := (hslot S0 hj₀S).trans hwj₀
  have hA0 : ∀ j, 0 ≤ (1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j)‖ :=
    fun j => by positivity
  have hterm : ∀ j ∈ S0, ((1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j)‖) *
      ∏ i ∈ S0.erase j, w i ≤
      (cL L u * dec L u (r / 2) + 3 * (L : ℝ) ^ 2 * cL L u ^ 2 * dec L u (r / 2)) := by
    intro j hjS
    have hQ0 : 0 ≤ ∏ i ∈ S0.erase j, w i := Finset.prod_nonneg fun i _ => hw0 i
    have hQ1 : ∏ i ∈ S0.erase j, w i ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => hw0 i) (fun i _ => hw i)
    have hA1 := sq_mul_norm_ThetaSBTheta_le_one hL hu0 hu1 (a 0) (a j)
    by_cases hjj : j = j₀
    · subst hjj
      have hA := sq_mul_norm_ThetaSBTheta_le_decay hL hu0 hu1 (a 0) (a j)
      have hA' : (1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j)‖ ≤
          3 * (L : ℝ) ^ 2 * cL L u ^ 2 * dec L u (r / 2) :=
        hA.trans (mul_le_mul_of_nonneg_left (dec_anti L hℓ hj) (by positivity))
      calc _ ≤ (3 * (L : ℝ) ^ 2 * cL L u ^ 2 * dec L u (r / 2)) * 1 :=
            mul_le_mul hA' hQ1 hQ0 (by positivity)
        _ ≤ _ := by
            have : 0 ≤ cL L u * dec L u (r / 2) := mul_nonneg hC hε
            linarith
    · have hjmem : j₀ ∈ S0.erase j := Finset.mem_erase.mpr ⟨fun h => hjj h.symm, hj₀S⟩
      have hQ : ∏ i ∈ S0.erase j, w i ≤ cL L u * dec L u (r / 2) := (hslot _ hjmem).trans hwj₀
      calc _ ≤ 1 * (cL L u * dec L u (r / 2)) := mul_le_mul hA1 hQ hQ0 zero_le_one
        _ ≤ _ := by
            have : 0 ≤ 3 * (L : ℝ) ^ 2 * cL L u ^ 2 * dec L u (r / 2) := by positivity
            linarith
  have hT2 : ∑ j ∈ S0, ((1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j)‖) *
      ∏ i ∈ S0.erase j, w i ≤
      ((k : ℝ) - 1) * (cL L u * dec L u (r / 2) + 3 * (L : ℝ) ^ 2 * cL L u ^ 2 * dec L u (r / 2)) := by
    calc _ ≤ ∑ _j ∈ S0, (cL L u * dec L u (r / 2) + 3 * (L : ℝ) ^ 2 * cL L u ^ 2 * dec L u (r / 2)) :=
          Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast NeZero.pos k
    linarith
  calc ((k : ℝ) - 1) * (1 - u)⁻¹ * ∏ i ∈ S0, w i +
        (1 - u)⁻¹ * ∑ j ∈ S0, ((1 - u) ^ 2 * ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) (a 0) (a j)‖) *
          ∏ i ∈ S0.erase j, w i
      ≤ ((k : ℝ) - 1) * (1 - u)⁻¹ * (cL L u * dec L u (r / 2)) +
        (1 - u)⁻¹ * (((k : ℝ) - 1) * (cL L u * dec L u (r / 2) +
          3 * (L : ℝ) ^ 2 * cL L u ^ 2 * dec L u (r / 2))) :=
        add_le_add (mul_le_mul_of_nonneg_left hP (mul_nonneg hk1 hτ))
          (mul_le_mul_of_nonneg_left hT2 hτ)
    _ = ((k : ℝ) - 1) * (1 - u)⁻¹ * (2 * cL L u + 3 * (L : ℝ) ^ 2 * cL L u ^ 2) * dec L u (r / 2) := by
        ring

end VarthetaDot

section PvdKer

variable {L : ℕ} [NeZero L] {k : ℕ} [NeZero k]

/-- The kernel of `𝒫·ϑ̇`: `(𝒫X)_{a₀} ϑ̇_{u,a} = Σ_c 1(c₀ = a₀) ϑ̇_{u,a} X_c` (closure lemma (c)). -/
def pvdKer (u : ℝ) (a c : Fin k → Z2 L) : ℂ := if c 0 = a 0 then varthetaDot L u a else 0

/-- **Closure lemma (c)**: `Σ_c pvdKer_{a,c} X_c = (𝒫X)_{a₀} ϑ̇_a`. -/
theorem sum_pvdKer (u : ℝ) (X : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) :
    ∑ c, pvdKer u a c * X c = Psum L X (a 0) * varthetaDot L u a := by
  unfold pvdKer Psum
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp [mul_comm]

/-- The hypotheses of the assembly for the kernel of `𝒫·ϑ̇` (`K1` `|ϑ̇| ≤ 2(k-1)(1-u)⁻¹`, `K2'` support
`c₀ = a₀`, `K3'` the decay of `ϑ̇` in `maxDist a`). -/
theorem pvdKer_hyps (hL : 3 ≤ L) (hk : 2 ≤ k) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {ρ : ℝ}
    (hρ : 0 < ρ) :
    (∀ a c : Fin k → Z2 L, ‖pvdKer u a c‖ ≤ 2 * ((k : ℝ) - 1) * (1 - u)⁻¹) ∧
    (∀ a c : Fin k → Z2 L, ρ ≤ (zdist2 L (c 0 - a 0) : ℝ) → ‖pvdKer u a c‖ ≤ 0) ∧
    (∀ a c : Fin k → Z2 L, ρ ≤ (KLoop.maxDist L a : ℝ) →
        ‖pvdKer u a c‖ ≤ ((k : ℝ) - 1) * (1 - u)⁻¹ *
          (2 * cL L u + 3 * (L : ℝ) ^ 2 * cL L u ^ 2) * dec L u (ρ / 2)) := by
  have h1u : 0 < 1 - u := by linarith
  have hC := cL_nonneg L u
  have hε := (dec_pos L u (ρ / 2)).le
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast NeZero.pos k
    linarith
  refine ⟨fun a c => ?_, fun a c hnear => ?_, fun a c hfar => ?_⟩
  · unfold pvdKer
    split_ifs
    · exact norm_varthetaDot_le hL hk hu0 hu1 a
    · simpa using mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk1) (inv_nonneg.2 h1u.le)
  · have hne : c 0 ≠ a 0 := by
      intro h
      rw [h, sub_self, zdist2_zero] at hnear
      simp at hnear
      linarith
    simp [pvdKer, hne]
  · unfold pvdKer
    split_ifs
    · exact norm_varthetaDot_le_decay hL hk hu0 hu1 a hρ hfar
    · simp only [norm_zero]
      positivity

end PvdKer

section KcalTrunc

variable (d : Sizes)

/-- **Closure lemma (a), the constant part `𝒦`**: from `KcalDecay` (`eq:bcal_k`) the far labels of `𝒦`
are `≤ W^{-D}`, eventually, uniformly in the time and the sign vector (deterministic). -/
theorem kcalTruncErr {κ c τ : ℝ} {E s t : ℕ → ℝ} (hmain : MainIndHyp d κ c τ E s t)
    (hK : KcalDecay κ) {k : ℕ} [NeZero k] (hk : 1 ≤ k) {τ₀ D : ℝ} (hτ₀ : 0 < τ₀) (hD : 0 < D)
    (u : ℕ → ℝ) (σ : ∀ n, Fin k → Bool) (hu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) :
    ∀ᶠ n : ℕ in atTop, ∀ a : Fin k → Z2 (d.L n),
      ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ ≤ (KLoop.maxDist (d.L n) a : ℝ) →
        ‖KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) a)‖ ≤ (d.W n : ℝ) ^ (-D) := by
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, -, -, -, -⟩ := hmain
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have h1 := hK hκ c hc k hk τ₀ D hτ₀ hD
  filter_upwards [hsizeN.eventually h1, hband] with n hn hb a ha
  have hu0 : 0 ≤ u n := (hs0 n).trans (hu n)
  have hu1 : u n < 1 := lt_of_le_of_lt (hut n) (ht1 n)
  have := hn (d.L n) (d.W n) (d.three_le_L n) (Sizes.size_eq d n).symm hb (E n) (hE n) (u n) hu0 hu1
    (σ n) a
  exact this (by simpa using ha)

end KcalTrunc

end LocalFormCalc

variable (d : Sizes)

/-- **`AltLocalForm` at one `m`** (`Fin 6`): the body of `AltLocalForm` (`RBM2D.Induction.StoppedEndDefs`)
with `m` fixed, all premises and quantifiers unchanged. -/
def AltLocalFormAt (κ c τ : ℝ) (E s t : ℕ → ℝ) (m : Fin 6) : Prop :=
  MainIndHyp d κ c τ E s t → DecayLoopPT d E s t → KcalDecay κ →
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (τ₀ D₀ : ℝ), 0 < τ₀ → 0 < D₀ →
  ∃ (K : ℕ) (C' : ℝ), 0 ≤ C' ∧
    ∀ (u : ℕ → ℝ) (σ : ℕ → Fin k → Bool), (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      (∀ n, Alternating (σ n)) →
    ∃ F : ∀ n, LocalForm (d.L n) (d.W n) k K,
      (∀ n b j q, ‖(F n).coef b j q‖ ≤ ((d.size n : ℕ) : ℝ) ^ C') ∧
      (∀ n, (F n).Local τ₀ (u n)) ∧
      (∀ n M, SumZero (d.L n) (fun b => (F n).eval (E n) (u n) M b)) ∧
      LabelDecayPT d E u F τ₀ D₀ ∧
      PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => Unit × (Fin k → Z2 (d.L n)))
        (fun n p ω => ‖altQB (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) m
            p.2 - (F n).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) p.2‖)
        (fun n _ _ => (d.W n : ℝ) ^ (-D₀))

/-- **The `m`-split of `AltLocalForm`**: if `AltLocalFormAt` holds for the six `m`, `AltLocalForm` holds. -/
theorem altLocalForm_of_at {κ c τ : ℝ} {E s t : ℕ → ℝ}
    (h : ∀ m : Fin 6, AltLocalFormAt d κ c τ E s t m) : AltLocalForm d κ c τ E s t :=
  fun hmain hdl hK k _ hk m τ₀ D₀ hτ₀ hD₀ => h m hmain hdl hK k hk τ₀ D₀ hτ₀ hD₀

/-- **The case `m = 4` (`ℬ₄ = [𝒬_u, ϴ_{u,σ}](𝓛-𝒦)`, `eq:case4_B`)**: for alternating `σ`
every `ξ_i = 1`, `ℬ₄` is a linear image of `𝓛 - 𝒦` through the kernel `𝔎` (`kerB4`), and the local
form is `𝒬_u` on the coefficients of `𝔎^{tr}(𝓛-𝒦)^{tr}`, truncated at `ρ = ℓ_u W^{τ₀}/8`. -/
theorem altLocalFormAt_four {κ c τ : ℝ} {E s t : ℕ → ℝ} : AltLocalFormAt d κ c τ E s t 4 := by
  intro hmain hdl _hK k _ hk τ₀ D₀ hτ₀ hD₀
  have hmain' := hmain
  obtain ⟨hκ, hE, hc, hτ, hs0, hst, ht1, hsize, hband, -, hrange, -, -, -⟩ := hmain'
  refine ⟨k, ((3 * k + 3 : ℕ) : ℝ), by positivity, fun u σ hu hut hσ => ?_⟩
  -- the constants
  set Dtr : ℝ := D₀ + ((k + 2 + 1 : ℕ) : ℝ) / c with hDtr
  have hkc : 0 < ((k + 2 + 1 : ℕ) : ℝ) / c := by positivity
  have hDtr0 : 0 < Dtr := by rw [hDtr]; linarith
  have hl1 := LocalFormCalc.lkTruncErr d hmain hdl (k := k) (by omega) hτ₀ hDtr0 u σ hu hut
  -- eventual facts
  obtain ⟨μ, hμ, hμb⟩ := LocalFormCalc.im_bounds hE hκ
  have hsizeN : Tendsto d.size atTop atTop := tendsto_natCast_atTop_iff.mp hsize
  have e1 : ∀ᶠ n : ℕ in atTop, 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ τ := by
    filter_upwards [((tendsto_rpow_atTop hτ).comp hsize).eventually_ge_atTop (1 / μ)] with n hn
    simp only [Function.comp] at hn
    rw [div_le_iff₀ hμ] at hn
    linarith
  have e2 : ∀ᶠ n : ℕ in atTop, 1 ≤ ((d.size n : ℕ) : ℝ) := hsize.eventually_ge_atTop 1
  have e3 : ∀ᶠ n : ℕ in atTop, 8 * (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧
      8 * LocalFormCalc.Qc k ≤ ((d.size n : ℕ) : ℝ) ∧
      4 * (k : ℝ) * LocalFormCalc.C5 ≤ ((d.size n : ℕ) : ℝ) := by
    filter_upwards [hsize.eventually_ge_atTop (8 * (k : ℝ)),
      hsize.eventually_ge_atTop (8 * LocalFormCalc.Qc k),
      hsize.eventually_ge_atTop (4 * (k : ℝ) * LocalFormCalc.C5)] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have e4 : ∀ᶠ n : ℕ in atTop, ((d.size n : ℕ) : ℝ) ^ (((3 * k + 7 : ℕ) : ℝ)) *
      Real.exp (-((d.W n : ℝ) ^ τ₀ / 320000)) ≤ (d.W n : ℝ) ^ (-D₀) :=
    LocalFormCalc.tail_eventually d hc (Nat.cast_nonneg _) (by norm_num) hτ₀ hband hsize
  have e5 : ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → W ^ 2 * L ^ 2 = N →
      ∀ E' : ℝ, |E'| ≤ 2 - κ → ∀ u' v : ℝ, 0 ≤ u' → u' ≤ v → v < 1 →
        ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ k →
          ‖KLoop.Kcal L W E' u' J‖ ≤ (N : ℝ) ^ (1 : ℝ) * ((RBM.Path.etaT E' v)⁻¹) ^ k :=
    exists_norm_Kcal_le_win κ hκ k 1 one_pos
  have e6 := hsizeN.eventually e5
  -- the bundle of eventual facts
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ ((d.size n : ℕ) : ℝ) ∧
      ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n ∧ 1 ≤ μ * ((d.size n : ℕ) : ℝ) ^ τ ∧
      (8 * (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧ 8 * LocalFormCalc.Qc k ≤ ((d.size n : ℕ) : ℝ) ∧
        4 * (k : ℝ) * LocalFormCalc.C5 ≤ ((d.size n : ℕ) : ℝ)) ∧
      ((d.size n : ℕ) : ℝ) ^ (((3 * k + 7 : ℕ) : ℝ)) * Real.exp (-((d.W n : ℝ) ^ τ₀ / 320000)) ≤
        (d.W n : ℝ) ^ (-D₀) ∧
      (∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → W ^ 2 * L ^ 2 = d.size n →
        ∀ E' : ℝ, |E'| ≤ 2 - κ → ∀ u' v : ℝ, 0 ≤ u' → u' ≤ v → v < 1 →
          ∀ J : LoopIdx (Z2 L), J.WF → 2 ≤ J.length → J.length ≤ k →
            ‖KLoop.Kcal L W E' u' J‖ ≤ ((d.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((RBM.Path.etaT E' v)⁻¹) ^ k) := by
    filter_upwards [e2, hrange, e1, e3, e4, e6] with n h2 h3 h1 h4 h5 h6
    exact ⟨h2, h3, h1, h4, h5, h6⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hev
  -- the radius and the assembled form
  set ρ : ℕ → ℝ := fun n => ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ / 8 with hρdef
  set Fg : ∀ n, LocalForm (d.L n) (d.W n) k k := fun n =>
    LocalFormCalc.asmF (u n) (ρ n) (LocalFormCalc.kerB4 (u n))
      (LocalFormCalc.lkF (σ n) (E n) (u n)) with hFg
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs0 n).trans (hu n)
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hℓ : ∀ n, 0 < ellT (d.L n) (u n) := fun n =>
    (ellT_pos_le (by have := d.three_le_L n; omega) (hu1 n)).1
  have hWpos : ∀ n, 0 < (d.W n : ℝ) := fun n => by exact_mod_cast d.W_pos n
  have hρpos : ∀ n, 0 < ρ n := fun n => by
    simp only [hρdef]
    have := hℓ n
    have := Real.rpow_pos_of_pos (hWpos n) τ₀
    positivity
  have hηpos : ∀ n, 0 < etaT (E n) (u n) := fun n =>
    etaT_pos (by linarith [hE n]) (hu1 n)
  -- the deterministic facts at every `n ≥ n₀`
  have key : ∀ n, n₀ ≤ n →
      1 ≤ ((d.size n : ℕ) : ℝ) ∧ ((d.L n : ℝ)) ^ 2 ≤ ((d.size n : ℕ) : ℝ) ∧
      (((d.L n * d.W n) ^ 2 : ℕ) : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧
      (1 - u n)⁻¹ ≤ ((d.size n : ℕ) : ℝ) ∧ (etaT (E n) (u n))⁻¹ ≤ ((d.size n : ℕ) : ℝ) ∧
      (∀ b : Fin k → Z2 (d.L n), ‖KLoop.Kcal (d.L n) (d.W n) (E n) (u n) (loopOf (σ n) b)‖ ≤
        ((d.size n : ℕ) : ℝ) * (etaT (E n) (u n))⁻¹ ^ k) ∧
      8 * (k : ℝ) ≤ ((d.size n : ℕ) : ℝ) ∧ 8 * LocalFormCalc.Qc k ≤ ((d.size n : ℕ) : ℝ) ∧
      4 * (k : ℝ) * LocalFormCalc.C5 ≤ ((d.size n : ℕ) : ℝ) ∧
      ((d.size n : ℕ) : ℝ) ^ (3 * k + 7) * LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) ≤
        (d.W n : ℝ) ^ (-D₀) := by
    intro n hn
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hn₀ n hn
    have hN0 : 0 < ((d.size n : ℕ) : ℝ) := by linarith
    have hx : ((d.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - u n := h2.trans (by linarith [hut n])
    refine ⟨h1, LocalFormCalc.L_sq_le_size d n, ?_, LocalFormCalc.inv_one_sub_le h1 hτ hx, ?_, ?_,
      h4.1, h4.2.1, h4.2.2, ?_⟩
    · have : ((d.L n * d.W n) ^ 2 : ℕ) = d.size n := by rw [Sizes.size_eq]; ring
      rw [this]
    · exact LocalFormCalc.eta_inv hN0 hx hμ (hμb n) h3
    · intro b
      have hwf : (loopOf (σ n) b).WF := by simp [loopOf, LoopIdx.WF]
      have hlen : (loopOf (σ n) b).length = k := by simp [loopOf, LoopIdx.length]
      have := h6 (d.L n) (d.W n) (d.three_le_L n) (d.W_pos n) (Sizes.size_eq d n).symm (E n)
        (hE n) (u n) (u n) (hu0 n) le_rfl (hu1 n) (loopOf (σ n) b) hwf (by omega) (by omega)
      rwa [Real.rpow_one] at this
    · have := h5
      rw [Real.rpow_natCast] at this
      have hd : LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) =
          Real.exp (-((d.W n : ℝ) ^ τ₀ / 320000)) := LocalFormCalc.dec_rho (hℓ n)
      rw [hd]
      exact this
  refine ⟨fun n => if n₀ ≤ n then Fg n else LocalFormCalc.zeroF, ?_, ?_, ?_, ?_, ?_⟩
  · -- the coefficient bound
    intro n b j q
    by_cases hn : n₀ ≤ n
    · simp only [hn, ↓reduceIte, hFg]
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      have := LocalFormCalc.four_coef (d.three_le_L n) (d.W_pos n) (hu0 n) (hu1 n) (ρ n) (σ n)
        hN1 hLN hτu hη (hηpos n) hKc hc1 b j q
      rwa [← Real.rpow_natCast] at this
    · simp only [hn, ↓reduceIte, LocalFormCalc.zeroF, norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · -- locality
    intro n
    by_cases hn : n₀ ≤ n
    · simp only [hn, ↓reduceIte, hFg]
      refine (LocalFormCalc.four_loc (u n) (ρ n) (σ n) (E n)).local τ₀ (u n) ?_
      have := hℓ n
      have := Real.rpow_pos_of_pos (hWpos n) τ₀
      simp only [hρdef]
      nlinarith [mul_pos (hℓ n) this]
    · simp only [hn, ↓reduceIte]
      intro b j q hq
      exact absurd rfl hq
  · -- sum-zero
    intro n M
    by_cases hn : n₀ ≤ n
    · simp only [hn, ↓reduceIte, hFg]
      exact LocalFormCalc.sumZero_asmF (d.three_le_L n) hk (hu0 n) (hu1 n) (ρ n) _ _ _ _ M
    · simp only [hn, ↓reduceIte]
      intro a₁
      simp [LocalFormCalc.eval_zeroF]
  · -- label decay (deterministic)
    unfold LabelDecayPT
    refine LocalFormCalc.perTimeDomAt_of_le d (fun n p ω => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn p ω
    obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
    simp only [hn, ↓reduceIte, hFg]
    by_cases hfar : ellT (d.L n) (u n) * (d.W n : ℝ) ^ τ₀ ≤ (KLoop.maxDist (d.L n) p.2 : ℝ)
    · simp only [hfar, ↓reduceIte, mul_one]
      have hρle : ρ n ≤ (KLoop.maxDist (d.L n) p.2 : ℝ) := by
        refine le_trans ?_ hfar
        simp only [hρdef]
        have := mul_pos (hℓ n) (Real.rpow_pos_of_pos (hWpos n) τ₀)
        linarith
      exact LocalFormCalc.four_far (d.three_le_L n) (d.W_pos n) (by linarith [hE n]) (hu0 n)
        (hu1 n) (hρpos n) (σ n) hN1 hLN hNLW hτu hη hKc hc3
        (le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 (by omega))
          (LocalFormCalc.dec_pos _ _ _).le) htail)
        (Sizes.seqHflow_isHermitian d n (u n) ω) p.2 hρle
    · simp only [hfar, ↓reduceIte, mul_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · -- the error: the stochastic kernel assembly `kernelAssembly_PT` with `𝔎 = kerB4`, `X = 𝓛 - 𝒦`
    have hδ0 : ∀ n, 0 ≤ LocalFormCalc.pdelta (d.L n) k (u n) *
        LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) := fun n =>
      mul_nonneg (LocalFormCalc.pdelta_nonneg _ _ (hu1 n)) (LocalFormCalc.dec_pos _ _ _).le
    have hK1 : ∀ᶠ n : ℕ in atTop, ∀ (a c' : Fin k → Z2 (d.L n)),
        ‖LocalFormCalc.kerB4 (u n) a c'‖ ≤ ((d.size n : ℕ) : ℝ) ^ 2 := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn a c'
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      have := (LocalFormCalc.kerB4_hyps (k := k) (d.three_le_L n) (hu0 n) (hu1 n) (ρ := 1) one_pos
        hτu).1 a c'
      refine this.trans ?_
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hK2 : ∀ᶠ n : ℕ in atTop, ∀ (a c' : Fin k → Z2 (d.L n)),
        ρ n ≤ (zdist2 (d.L n) (c' 0 - a 0) : ℝ) → (KLoop.maxDist (d.L n) c' : ℝ) < ρ n →
          ‖LocalFormCalc.kerB4 (u n) a c'‖ ≤ LocalFormCalc.pdelta (d.L n) k (u n) *
            LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn a c' h1 h2
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      exact (LocalFormCalc.kerB4_hyps (k := k) (d.three_le_L n) (hu0 n) (hu1 n) (hρpos n)
        hτu).2.1 a c' h1
    have hK3 : ∀ᶠ n : ℕ in atTop, ∀ (a c' : Fin k → Z2 (d.L n)),
        ρ n ≤ (KLoop.maxDist (d.L n) a : ℝ) → (KLoop.maxDist (d.L n) c' : ℝ) < ρ n →
          ‖LocalFormCalc.kerB4 (u n) a c'‖ ≤ LocalFormCalc.pdelta (d.L n) k (u n) *
            LocalFormCalc.dec (d.L n) (u n) (ρ n / 2) := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn a c' h1 h2
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      exact (LocalFormCalc.kerB4_hyps (k := k) (d.three_le_L n) (hu0 n) (hu1 n) (hρpos n)
        hτu).2.2 a c' h1
    have hX : ∀ᶠ n : ℕ in atTop, ∀ (ω : Sizes.SeqΩ d) (c' : Fin k → Z2 (d.L n)),
        ‖lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) c'‖ ≤
          ((d.size n : ℕ) : ℝ) ^ (k + 2) := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn ω c'
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      have h2 := LocalFormCalc.norm_lkTensor_le (d.W_pos n) (by linarith [hE n]) (hu1 n)
        (Sizes.seqHflow_isHermitian d n (u n) ω) (σ n) c' hη hNLW hN1 (hKc c')
      refine h2.trans ?_
      have hk2 : (2 : ℝ) ≤ ((d.size n : ℕ) : ℝ) := by
        have : (2 : ℝ) ≤ 8 * (k : ℝ) := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        linarith
      calc 2 * ((d.size n : ℕ) : ℝ) ^ (k + 1) ≤ ((d.size n : ℕ) : ℝ) * ((d.size n : ℕ) : ℝ) ^ (k + 1) :=
            mul_le_mul_of_nonneg_right hk2 (by positivity)
        _ = ((d.size n : ℕ) : ℝ) ^ (k + 2) := by ring
    have hδ : ∀ᶠ n : ℕ in atTop, (1 + ((d.size n : ℕ) : ℝ) ^ k) *
        (((d.size n : ℕ) : ℝ) ^ k * (LocalFormCalc.pdelta (d.L n) k (u n) *
          LocalFormCalc.dec (d.L n) (u n) (ρ n / 2)) * ((d.size n : ℕ) : ℝ) ^ (k + 2)) ≤
        (d.W n : ℝ) ^ (-D₀) / 2 := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
      obtain ⟨hN1, hLN, hNLW, hτu, hη, hKc, hc1, hc2, hc3, htail⟩ := key n hn
      exact LocalFormCalc.four_tail (d.three_le_L n) (hu0 n) (hu1 n) hN1 hLN hτu hc2 htail
    have hFXeq : ∀ n (ω : Sizes.SeqΩ d) (c' : Fin k → Z2 (d.L n)),
        (LocalFormCalc.lkF (σ n) (E n) (u n)).eval (E n) (u n) (Sizes.seqHflow d n (u n) ω) c' =
          lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) c' :=
      fun n ω c' => LocalFormCalc.eval_lkF _ _ _ _ c'
    have h := LocalFormCalc.kernelAssembly_PT d (D₀ := D₀) hc hband hsize (aK := 2) (aX := k + 2)
      (K := k) (E := E) (u := u) (ρ := ρ)
      (δ := fun n => LocalFormCalc.pdelta (d.L n) k (u n) * LocalFormCalc.dec (d.L n) (u n) (ρ n / 2))
      (fun n => LocalFormCalc.kerB4 (u n))
      (fun n => LocalFormCalc.lkF (σ n) (E n) (u n))
      (fun n ω => lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n))
      hFXeq hu0 hu1 hδ0 hK1 hK2 hK3 hX hδ hl1
    refine LocalFormCalc.perTimeDomAt_congr_left d ?_ h
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn p ω
    simp only [hn, ↓reduceIte, hFg]
    have hB4 : (fun a' => B4 (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) a') =
        fun a' => ∑ c', LocalFormCalc.kerB4 (u n) a' c' *
          lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) c' := by
      funext a'
      exact LocalFormCalc.commutator_eq_kerB4 (d.three_le_L n) hk (hu0 n) (hu1 n)
        (by linarith [hE n]) (hσ n) _ a'
    change ‖Qop (d.L n) (u n) (fun a' => ∑ c', LocalFormCalc.kerB4 (u n) a' c' *
          lkTensor (d.L n) (d.W n) (E n) (u n) (Sizes.seqHflow d n (u n) ω) (σ n) c') p.2 -
        (LocalFormCalc.asmF (u n) (ρ n) (LocalFormCalc.kerB4 (u n))
          (LocalFormCalc.lkF (σ n) (E n) (u n))).eval (E n) (u n)
          (Sizes.seqHflow d n (u n) ω) p.2‖ =
      ‖Qop (d.L n) (u n) (fun a' => B4 (d.L n) (d.W n) (E n) (u n)
          (Sizes.seqHflow d n (u n) ω) (σ n) a') p.2 -
        (LocalFormCalc.asmF (u n) (ρ n) (LocalFormCalc.kerB4 (u n))
          (LocalFormCalc.lkF (σ n) (E n) (u n))).eval (E n) (u n)
          (Sizes.seqHflow d n (u n) ω) p.2‖
    rw [hB4]

end RBM.Ind
