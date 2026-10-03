# The paper and the Lean proof: detailed differences

**Paper.** S. Dubova, K. Yang, H.-T. Yau and J. Yin, *Delocalization of two-dimensional random band
matrices*, arXiv:2503.07606, in the version `paper/DubovaYangYauYin_RBM2D_Lean_version.pdf` of this
repository (TeX source in `paper/tex/`). Page, equation and theorem numbers below refer to this PDF.

**Cited works.** [32] = B. Landon, P. Sosoe, H.-T. Yau, *Fixed energy universality of Dyson Brownian
motion*, Adv. Math. 346 (2019), in the form of arXiv:1609.09011v4. [25] = L. Erdős, H.-T. Yau, *A dynamical
approach to random matrix theory*, AMS 2017. [26] = L. Erdős, H.-T. Yau, J. Yin, *Rigidity of eigenvalues of
generalized Wigner matrices*, Adv. Math. 229 (2012). [45] = C. Xu, F. Yang, H.-T. Yau, J. Yin, *Bulk
universality and quantum unique ergodicity for random band matrices in high dimensions*, Ann. Probab. 52
(2024). [50] = H.-T. Yau, J. Yin, *Delocalization of one-dimensional random band matrices*, arXiv:2501.01718.

**Lean.** The library is `RBM2D` (Lean 4.34.0, Mathlib v4.34.0); its declarations are in the namespace `RBM`.
Every name below that starts with `RBM.` is a declaration of this library, used directly or indirectly by
the proofs of the five main theorems or by the compiled instances of §1. Other names (such as
`Matrix.trace`, `Matrix.IsHermitian.eigenvalues`, `ProbabilityTheory.gaussianReal`) are from Mathlib. Lean
text quoted below is copied from the source files by a script, without docstrings.

---

## 1. What is proved

**The model.** A *size sequence* is a term `d : RBM.Gauss.Sizes` (block numbers `L n ≥ 3`, block widths
`W n ≥ 1`). The matrix dimension is `d.size n = (W n · L n)²`, the paper's `N = W²L²` (p. 4). The index
set `Z²_{WL}` is `RBM.Gauss.Idx L W = RBM.Z2 (W * L)`, with `RBM.Z2 m = ZMod m × ZMod m`. The block
`𝓘_a^{(2)}` is `RBM.Iblk L W a`, the matrix `E_a` of (7) is `RBM.Epaper L W a`, and `S^{(B)}` is `RBM.SB L`,
the circulant matrix with value `1/5` on the five points `(0,0), (±1,0), (0,±1)` (`RBM.sbSupport`), which for
`L ≥ 3` are the points at periodic `L¹` distance `≤ 1`. The matrix `RBM.Gauss.Xmat L W ω` is Hermitian
(`RBM.Gauss.Xmat_isHermitian`); its real coordinates are independent centred Gaussians, `RBM.Gauss.P L W` (the
infinite product of `ProbabilityTheory.gaussianReal 0 (gvar c)`), with the variances of §2.2. For a size
sequence, `d.seqP` is the product of these laws over all `n`, and the law of the matrix `d.seqXmat n` is
`RBM.Gauss.P (d.L n) (d.W n)` (`RBM.Gauss.Sizes.seqP_map_slice`). All probabilities are `d.seqP` of sets.
The bandwidth condition (1), together with `N → ∞`, is `Admissible`.

```lean
-- namespace RBM.Gauss (`size` is `RBM.Gauss.Sizes.size`, with `d : Sizes`)
structure Sizes where
  L : ℕ → ℕ
  W : ℕ → ℕ
  three_le_L : ∀ n, 3 ≤ L n
  W_pos : ∀ n, 0 < W n

def size (n : ℕ) : ℕ := (d.W n * d.L n) ^ 2

noncomputable def svar (i j : Idx L W) : ℝ :=
  if (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L
  then (5 : ℝ)⁻¹ * (W : ℝ)⁻¹ ^ 2 else 0

-- namespace RBM.Endpoints
def Admissible (𝔠 : ℝ) (d : Sizes) : Prop :=
  Tendsto (fun n => d.size n) atTop atTop ∧
    ∀ᶠ n in atTop, ((d.size n : ℕ) : ℝ) ^ 𝔠 ≤ (d.W n : ℝ)
```

**The theorems.** The statements `decol`, `locSC`, `QUE`, `QDiff`, `BUniv` are in `RBM2D/Endpoints.lean`
(Appendix A). The four theorems without hypothesis are proved in `RBM2D/Main/Endpoints.lean`, and
`bUniv_holds` in `RBM2D/Main/BUnivHolds.lean`.

| Paper | Lean | Hypotheses other than parameters |
|---|---|---|
| Theorem 2.2 (delocalization) | `RBM.Endpoints.decol_holds : RBM.Endpoints.decol` | none |
| Theorem 2.3 (local semicircle law: (4), (5)) | `RBM.Endpoints.locSC_holds : RBM.Endpoints.locSC` | none |
| Theorem 2.4 (generalized QUE: (8), (9)) | `RBM.Endpoints.QUE_holds : RBM.Endpoints.QUE` | none |
| Theorem 2.5 (quantum diffusion: (10)–(13)) | `RBM.Endpoints.QDiff_holds : RBM.Endpoints.QDiff` | none |
| Theorem 2.6 (bulk universality: (17)) | `RBM.Endpoints.bUniv_holds : RBM.Univ.L32 → RBM.Endpoints.BUniv` | `RBM.Univ.L32` |

"Parameters" are `𝔠 > 0` and a size sequence `d` with `Admissible 𝔠 d`; `κ, τ, D > 0` (and `0 < τ < 𝔠/2` in
Theorem 2.4); in Theorem 2.6 also `k ≥ 1`, `|E| ≤ 2 − κ` and the test function `O`. The spectral parameter
`z` of Theorems 2.3 and 2.5, and the energy `E`, the block `a` and the block set `A` of Theorem 2.4, are bound
inside the statements (§2.5).

**The single external input.** Theorem 2.6 is proved from `RBM.Univ.L32`, which is [32, Theorem 2.2] for
complex Hermitian matrices, written at unit density (§4). It is a hypothesis of `bUniv_holds`, not an axiom.
Theorems 2.2–2.5 use no external input. The Lean proof has no other input: the only hypothesis of
`bUniv_holds` is `L32`, and the axioms are the three listed below. The results that the paper quotes from [50],
[25], [45] and [26] are not assumed in Lean; the Lean proofs of the corresponding statements are listed in §5.7.

**Axioms.** The command `#assert_rbm_axioms` (file `RBM2D/Test/Axioms.lean`, run as the last line of
`RBM2D.lean`) fails the build unless every declaration in the namespace `RBM` depends only on `propext`,
`Classical.choice`, `Quot.sound`. The command `#print axioms` on the five theorems prints

```
'RBM.Endpoints.decol_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.locSC_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.QUE_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.QDiff_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the same for `RBM.Endpoints.admissible_witnessSizes`, `RBM.Endpoints.locSC_holds_instance` and
`RBM.Endpoints.mSC_eq_msc`.

**The statements are not vacuous.** `RBM.Endpoints.witnessSizes` has `L n = n + 3`, `W n = (n + 3)²`, hence
`N = (n + 3)⁶ → ∞` and `W = N^{1/3}`; `RBM.Endpoints.admissible_witnessSizes : Admissible (1/3) witnessSizes`
is compiled. `RBM.Endpoints.locSC_holds_instance` applies Theorem 2.3 to `witnessSizes` at `𝔠 = 1/3`,
`κ = 1`, `τ = 1/2`, `D = 1`, with no hypothesis left. Two examples in `RBM2D/Main/BUnivHolds.lean` apply
`bUniv_holds` to `witnessSizes` at `𝔠 = 1/3`, `k = 1`, `κ = 1`, the energies `E = 0` and `E = 1` (the edge of
the window) and the smooth compactly supported bump function `RBM.Univ.Step1CondCheck.bump`; only `L32`
remains a hypothesis. Theorems 2.2, 2.4 and 2.5 have no separate compiled instance; their hypotheses
(`Admissible 𝔠 d`, and `0 < τ < 𝔠/2` in Theorem 2.4) are satisfied by `witnessSizes`.

---

## 2. Differences between the statements

Each entry gives the paper's wording, the Lean form and the relation. "Equivalent": each statement implies the
other for the full family of parameters. "Lean stronger": the Lean statement implies the paper's.
"Identical": the same statement up to notation.

### 2.1 Size sequences instead of "there exists `N₀`" (equivalent, with §3)

- **Paper** (p. 5, Theorems 2.2–2.5 and (1)): "Suppose that `W ≥ N^𝔠` for some fixed constant `𝔠 > 0`. Then
  for any `κ, τ, D > 0`, there exists `N₀` such that for all `N ⩾ N₀`" the estimate holds; Theorem 2.6 has
  `lim_{N→∞}`.
- **Lean.** `∀ 𝔠 > 0, ∀ d : Sizes, Admissible 𝔠 d → ∀ κ τ D > 0, ∀ᶠ n in atTop, …`, with `N = d.size n`.
  `Admissible 𝔠 d` contains `d.size n → ∞` and `N^𝔠 ≤ W n` for large `n`. The divergence of the size is explicit
  because "for large `n`" along a bounded sequence of sizes has no content; in the paper it is part of
  "as `N → ∞`" (p. 4).

### 2.2 Blocks, variance profile and diagonal (identical; standard reading on the diagonal)

- **Paper** (pp. 4–5): `Z_L ≃ {1,…,L}`, `𝓘_{a(i)} = [(a(i) − 1)W + 1, a(i)W]`; `S^{(B)}_{ab} = (1/5)·1(|a − b|_L ≤ 1)`,
  `(S_W)_{ij} = W^{-2}`, `S = S^{(B)} ⊗ S_W`; "the entries `H_xy ∼ CN(0, S_xy)` are independent centred complex
  Gaussian random variables" up to `H_xy = conj H_yx`.
- **Lean.** Blocks are zero-based: `RBM.Iblk L W a` is the product of the two intervals `{a_i.val · W + α : α < W}`
  (`RBM.mem_Iblk : x ∈ Iblk L W a ↔ (RBM.split L W x).1 = a`; `RBM.splitEquiv : Z2 (W * L) ≃ BlockIndex L W`).
  The variance is `RBM.Gauss.svar` (§1), identified with `(S^{(B)} ⊗ S_W)_{ij}` by
  `RBM.Gauss.svar_cast_eq_Spaper`. The entry above the diagonal is `ω(i,j,true) + i·ω(i,j,false)` (each real
  coordinate has variance `S_ij/2`), the entry below is fixed by `H_ji = conj H_ij`, and a diagonal entry is the real
  coordinate `ω(i,i,true)`, of variance `S_ii`.
- **Relation.** The blocks are identical under `a(i) ↦ a(i) − 1`. A diagonal entry satisfies `H_xx = conj H_xx`,
  so it is real, and `E|H_xx|² = S_xx` fixes its variance; everywhere `E|H_xy|² = S_xy`. The five-point form
  of `S^{(B)}` needs `L ≥ 3`, as the paper assumes (p. 4).

### 2.3 Eigenvalue and eigenvector labels (Lean stronger)

- **Paper** (pp. 4–6): `λ_1 ≤ … ≤ λ_N` with unit eigenvectors `ψ_k`, `Hψ_k = λ_kψ_k`.
- **Lean.** `RBM.Endpoints.IsOrthoEigenbasis H μ ψ`: the `ψ k` are orthonormal and `H ψ_k = μ_k ψ_k`, with no
  order on `μ`. The failure events `RBM.Endpoints.decolEvent`, `queBad`, `que2Bad` (Appendix A) quantify
  over every such pair `(μ, ψ)`; for example `queBad` is "there is an orthonormal eigenbasis and `k, k'` in
  the window with `N^{-τ/6} ≤ |N ψ_k^*(E_a − N^{-1})ψ_{k'}|²`".
- **Relation.** The paper's failure event, for any choice of its eigenvectors, is contained in the Lean
  failure event, so the Lean bound implies the paper's. The order is irrelevant, since each statement takes a
  maximum over all labels. No simplicity of the spectrum is used.

### 2.4 Failure probability instead of success probability (equivalent)

- **Paper** (Theorems 2.2, 2.3, 2.5): `P(success) ⩾ 1 − N^{-D}`. Theorem 2.4: `P(bad event) ≤ N^{-τ/6}`.
- **Lean.** `d.seqP {ω | ¬ …} ≤ ENNReal.ofReal (N^{-D})`, the set being the exact complement of the paper's
  success event (for example `¬ decolEvent …`); in Theorem 2.4 the bad event itself.
- **Relation.** For a measurable event `B`, `P(B) ≥ 1 − x` if and only if `P(Bᶜ) ≤ x`. Without measurability,
  `d.seqP` of a set is its outer measure, and `1 ≤ P(B) + P(Bᶜ)` still gives `P(B) ≥ 1 − N^{-D}`.

### 2.5 `N₀` uniform over `z`, `E`, `a`, `A` (equivalent, with §3)

- **Paper.** Theorem 2.3 (p. 5): "for any `z` of the form `z = E + iη`, `|E| ≤ 2 − κ`, `1 ≥ η ≥ N^{-1+τ}`, there
  exists `N₀` such that for all `N ⩾ N₀`". The domain of `z` depends on `N`, so `N₀` cannot depend on `z`.
  Theorem 2.5 is under the assumptions of Theorem 2.3. In (8), (9) (p. 6) the maxima `max_{E:|E|<2−κ} max_a`,
  `max_E max_A` stand outside the probability, with one `N₀`.
- **Lean.** `∀ᶠ n in atTop, ∀ z, RBM.Endpoints.locDomain (d.size n) κ τ z → …`; in `QUE`:
  `∀ᶠ n, ∀ E, |E| < 2 − κ → (∀ a, …) ∧ (∀ A, A.Nonempty → …)`; Theorem 2.5 has `∀ σ : Bool` (the cases
  `G, G†` and `G, G`) inside.
- **Relation.** Equivalent to "for every sequence `z_n`, `E_n`, `a_n`, `A_n` in the domain", and to the paper's
  uniform form (§3). The step from sequences to a bound uniform in the parameter is the compiled diagonal
  argument `RBM.Endpoints.EndpointsFromSTO_eventually_forall_of_sections` (a property that holds for large `n`
  along every section `s n ∈ Z n` holds eventually for all points of `Z n`), used for (12), (13).

### 2.6 (9): the weak inequality and the case `A = ∅` (Lean stronger)

- **Paper** (p. 6, (9)): for any `A ⊂ Z_L²`, `P(max_{k∈𝒥_E} |Σ_{a∈A} Σ_{x∈𝓘_a} |ψ_k(x)|² − |A|W²/N| >
  |A|W²/N^{1+τ/6}) ≤ N^{-τ/6}`. For `A = ∅` the event reads `0 > 0` and is empty; the proof says so (p. 8).
- **Lean.** `RBM.Endpoints.que2Bad` has the weak inequality `|A|W²/N^{1+τ/6} ≤ |…|`, and `QUE` states the bound
  for every `A` with `A.Nonempty`. The event in (8), `RBM.Endpoints.queBad`, has `N^{-τ/6} ≤ |…|²`, as in the
  paper; the window `𝒥_E` is `RBM.Endpoints.window`, the condition (6) is `τ < 𝔠/2`. Theorem 2.4 has no `D`.
- **Relation.** For `A ≠ ∅` the paper's event is contained in the Lean event with the same threshold, so the
  Lean bound implies the paper's. For `A = ∅` the paper's probability is `0`; the Lean statement omits this
  trivial case (with the weak inequality the event for `A = ∅` is `0 ≤ 0` and holds whenever some `k` is in the
  window).

### 2.7 `m(z)`, `ℓ(z)`, `M_η`, `Tr`, `Θ_ξ` and (12), (13) (identical)

- **Paper** (pp. 4–6, 15): `m(z) = ∫_{-2}^{2} (2π)^{-1}√((4 − x²)_+)/(x − z) dx = (−z + √(z² − 4))/2`;
  `ℓ(z) = min(η^{-1/2}, L) + 1`, `M_η = W²ℓ(z)²η`; `Tr` is the trace of the `N × N` matrix;
  `Θ_ξ = 1/(1 − ξS^{(B)})` for `|ξ| < 1`; (12): `max_{a,b} |E Tr G E_a G^† E_b − W^{-2}(|m|²/(1 − |m|²S^{(B)}))_{ab}| ≤
  M_η^{-3}W^τ`, and (13) the same with `G, m²`.
- **Lean.** `RBM.Endpoints.mSC z` is the integral, and `RBM.Endpoints.mSC_eq_msc` shows `mSC z = RBM.msc z` for
  `0 < Im z`, where `RBM.msc z` is the root of `m² + zm + 1 = 0` with `Im m > 0` (the branch of the closed
  form). `RBM.ellz L z = min (Im z ^ (-1/2)) L + 1`, `RBM.Meta L W z = W² · ellz L z ^ 2 · Im z`. `Tr` is
  `Matrix.trace`, not normalized. `RBM.Theta L ξ = Ring.inverse (1 − ξ • SB L)`; since `‖msc z‖ < 1` for
  `0 < Im z` (`RBM.norm_msc_lt_one`), the matrices with `ξ = |m|²` and `ξ = m²` are invertible, and
  `RBM.Endpoints.profile` is `W^{-2}(ξ/(1 − ξS^{(B)}))_{ab}`. The quantity `max_{x,y} |(G(z) − m(z))_{xy}|` is
  `‖Gn − (if x = y then mSC z else 0)‖`, with `RBM.Endpoints.Gn` the Green function `(H − z)^{-1}` at index `n`.
  In (12), (13): `∀ a b, ‖∫ ω, trGEGE d n ω z σ a b ∂d.seqP − profile … σ a b‖ ≤ Meta … ^ (-3 : ℤ) * W ^ τ`. The
  integrand is bounded for `Im z > 0` (`RBM.Gauss.norm_green_le`: `‖G(z)‖ ≤ (Im z)^{-1}` for Hermitian `H`), so
  the integral is the expectation.

### 2.8 Correlation functions and the GUE side of (17) (equivalent; identical)

- **Paper** (pp. 8–9): `ρ_H^{(k)}` is the `k`-marginal of the joint density `ρ_H^{(N)}` of the unordered
  eigenvalues; (17) is `lim ∫ dα 𝒪(α){(ρ_H^{(k)} − ρ_GUE^{(k)})(E + α/N)} = 0`. `ρ_GUE^{(k)}` is that of the GUE
  matrix of dimension `N = W²L²` with the law of `H_∞` for the Ornstein–Uhlenbeck flow
  `dH_t = −H_t dt/2 + N^{-1/2}dB_t`, for which `E|h_ij|² = 1/N`.
- **Lean.** `RBM.Endpoints.kPoint k O E λ = N^k(N − k)!/N! · Σ_{f : Fin k ↪ ι} O(N(λ_{f(1)} − E), …)` with
  `N = Fintype.card ι`; `BUniv` says that the difference of the expectations of `kPoint` for the band matrix and
  for the GUE matrix tends to `0` (Appendix A). `RBM.Endpoints.gueP L W` is the law of independent Gaussian
  coordinates with variance `1/N` on the diagonal and `1/(2N)` for each real and imaginary part off the diagonal
  (`RBM.Endpoints.gueVar`), so `RBM.Gauss.Xmat L W` under `gueP L W` is a GUE matrix with `E|h_ij|² = 1/N`.
- **Relation.** If the joint density of the symmetrized eigenvalues exists, then `∫ 𝒪(α) ρ^{(k)}(E + α/N) dα
  = E[N^k/(N(N−1)⋯(N−k+1)) · Σ_{distinct i} 𝒪(N(λ_{i_1} − E), …)]` (standard, not compiled); the Lean
  definition does not presuppose a density. The GUE side is identical: the Lean compares with the GUE matrix,
  not with an explicit eigenvalue density.

### 2.9 Test functions; one probability space (identical, equivalent)

- **Paper** (p. 9): "test function `𝒪 ∈ C_c^∞(ℝ^k)`"; a matrix `H` of dimension `N` for each `N`.
- **Lean.** `O : (Fin k → ℝ) → ℝ` with `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O` (smooth, not the analytic index
  `ω`) and `HasCompactSupport O`: identical for real-valued `𝒪`; complex-valued ones follow by linearity. One product
  measure `d.seqP` carries the coordinates of all indices `n`; the matrix at index `n` reads only level `n`
  and has the paper's law (`RBM.Gauss.Sizes.seqP_map_slice`), and every statement concerns one index at a
  time: equivalent (§3).

---

## 3. Uniformity in the size parameters

**The two forms.** In the paper `N₀` depends only on the fixed parameters (`𝔠, κ, τ, D`, and `τ` of (6) for
Theorem 2.4; for Theorem 2.6 also `k, E, 𝒪` and the accuracy), not on `(W, L)`: the estimate holds for all
`(W, L)` with `L ≥ 3`, `W ≥ N^𝔠`, `N = W²L² ≥ N₀`. The Lean statements say: for every size sequence `d` with
`Admissible 𝔠 d`, for all large `n`. The two forms are equivalent; the argument below is a paper argument and
is not compiled.

**Uniform ⇒ Lean.** Let `Admissible 𝔠 d`. For large `n`, `N = d.size n ≥ N₀` and `N^𝔠 ≤ W n`, so `(W n, L n)`
is one of the pairs of the uniform statement. The law of `d.seqXmat n` under `d.seqP` is the paper's law for
this pair (`RBM.Gauss.Sizes.seqP_map_slice`), and every event and quantity in the statements is a function of
this matrix. Hence the bound holds for large `n`.

**Lean ⇒ uniform.** Suppose that the uniform statement fails for some fixed parameters. Then for every `N₀`
there is a pair `(W, L)` with `L ≥ 3`, `N = W²L² ≥ N₀`, `W ≥ N^𝔠`, at which the estimate fails (for some `z`,
`E`, `a` or `A` where these occur). Choose pairs `(W_j, L_j)` with `N_j ≥ j`, and put `d.L j = L_j`,
`d.W j = W_j`. This is a size sequence, `d.size j = N_j → ∞` and `N_j^𝔠 ≤ W_j` for all `j`, so
`Admissible 𝔠 d` holds, and the estimate fails at every index `j`, contradicting the Lean theorem. (No filler
sequence is needed: a size sequence is arbitrary, and `d.size n` is exactly the matrix dimension.) For
Theorem 2.6 the same gluing is applied to a subsequence on which the difference in (17) stays above some
`ε > 0`.

**Remark.** If `𝔠 ≥ 1/2` no pair is admissible: `N^𝔠 ≥ N^{1/2} = WL ≥ 3W > W`. So the theorems concern
`0 < 𝔠 < 1/2`; for example `L ≡ 3` with `W → ∞` is allowed.

---

## 4. The external input [32]

The paper uses one result from the literature that the Lean proof does not prove: [32, Theorem 2.2], in Step 1
of the proof of Theorem 2.6 (p. 9, the limit (18)). In Lean it is the hypothesis `RBM.Univ.L32` of
`RBM.Endpoints.bUniv_holds`.

### 4.1 The Lean statement

Namespace `RBM.Univ` (directory `RBM2D/Universality/`). `IsRegular32` is [32, Definition 2.1] (`mV` is the
Stieltjes transform of `V`), `IsFreeConv32` is [32, (2.5)], `dbmMat` is [32, (2.1)] with the GOE replaced by
the GUE, and `rhoSC` is [32, (2.4)]; `kPoint` is in §2.8 and Appendix A.

```lean
def IsRegular32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (g G c C CV : ℝ) : Prop :=
  (∀ E η : ℝ, |E| ≤ G → g ≤ η → η ≤ 10 →
      c ≤ (mV v ⟨E, η⟩).im ∧ (mV v ⟨E, η⟩).im ≤ C) ∧
    ∀ i, |v i| ≤ (Fintype.card ι : ℝ) ^ CV

def IsFreeConv32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (t : ℝ) (m : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 < (m z).im ∧
    m z = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m z)⁻¹

def L32 : Prop :=
  ∀ d : Sizes, Tendsto (fun n => d.size n) atTop atTop →
  ∀ (δ σ q c C CV : ℝ), 0 < δ → 0 < σ → 0 < q → q < 1 → 0 < c →
  ∀ (g G t E : ℕ → ℝ) (v : ∀ n, Idx (d.L n) (d.W n) → ℝ) (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ),
    (∀ᶠ n in atTop,
      ((d.size n : ℕ) : ℝ) ^ δ / ((d.size n : ℕ) : ℝ) ≤ g n ∧
      g n ≤ ((d.size n : ℕ) : ℝ) ^ (-δ) ∧ G n ≤ ((d.size n : ℕ) : ℝ) ^ (-δ) ∧
      g n * ((d.size n : ℕ) : ℝ) ^ σ ≤ t n ∧ t n ≤ ((d.size n : ℕ) : ℝ) ^ (-σ) * G n ^ 2 ∧
      |E n| ≤ q * G n ∧
      IsRegular32 (v n) (g n) (G n) c C CV ∧ IsFreeConv32 (v n) (t n) (m n) ∧
      Tendsto (fun η : ℝ => (m n ⟨E n, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ n))) →
    ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
        Tendsto (fun n =>
          (∫ ω, kPoint k (fun α => O (ρ n • α)) (E n)
              (dbmMat_isHermitian (d.L n) (d.W n) (v n) (t n) ω).eigenvalues
              ∂(gueP (d.L n) (d.W n))) -
          (∫ ω, kPoint k (fun α => O (rhoSC (E n) • α)) (E n)
              (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues ∂(gueP (d.L n) (d.W n))))
          atTop (𝓝 0)
```

In words: along a size sequence with `N = (W n L n)² → ∞`, if for large `n` the diagonal matrix `V_n` is
`(g, G)`-regular, `g N^σ ≤ t ≤ N^{-σ}G²`, `|E| ≤ qG`, `m n` solves [32, (2.5)] and `ρ n` is the density
[32, (2.6)], then the two dilated `k`-point functionals differ by `o(1)`.

### 4.2 How it matches [32, Theorem 2.2] in the form of arXiv:1609.09011v4

[32] considers `H_t = V + √t W` with `V` a deterministic diagonal matrix and `W` a GOE matrix. Its (2.7) is
`p^{(k)}_{H_t}(λ_1,…,λ_k) = ∫ p^{(N)}_{H_t}(λ_1,…,λ_N) dλ_{k+1}⋯dλ_N`, where `p^{(N)}_{H_t}` is the
symmetrized eigenvalue probability density. Theorem 2.2: if `V` is `(g, G)`-regular (Definition 2.1),
`g N^σ ≤ t ≤ N^{-σ}G²` (2.8) and `|E| ≤ qG`, then there is `κ > 0` such that for every `k` and `O ∈ C_c^∞(ℝ^k)` there is `C > 0` with

```
| ρ_{fc,t}(E)^{-k} ∫ O(α) p^{(k)}_{H_t}(E + α/(Nρ_{fc,t}(E))) dα
  − ρ_{sc}(E)^{-k} ∫ O(α) p^{(k)}_{GOE}(E + α/(Nρ_{sc}(E))) dα | ≤ C N^{-κ}.        (2.9)
```

- **The density factors.** In arXiv:1609.09011v4 the two integrals of (2.9) carry the prefactors
  `ρ_{fc,t}(E)^{-k}` and `ρ_{sc}(E)^{-k}`; the earlier version arXiv:1609.09011v3 has no such prefactors. The substitution
  `α = ρβ` gives `ρ^{-k} ∫ 𝒪(α) p^{(k)}(E + α/(Nρ)) dα = ∫ 𝒪(ρβ) p^{(k)}(E + β/N) dβ`: each side's test
  function is dilated by that side's own density. This is the form of `L32`, in the eigenvalue-sum form `kPoint`
  (§2.8): `kPoint k (fun α => O (ρ n • α)) (E n)` on the first side and
  `kPoint k (fun α => O (rhoSC (E n) • α)) (E n)` on the second.
- **The complex Hermitian case.** [32] states and proves its results for the real symmetric case. The Remark
  after Theorem 2.2 in arXiv:1609.09011v4 states that the methods and results hold also for the complex
  Hermitian case, with essentially only notational changes, and the abstract names the GOE and the GUE. `L32` is
  the statement for the complex Hermitian case: `dbmMat` is `V + √t X`, with `X = RBM.Gauss.Xmat` under the GUE
  law `RBM.Endpoints.gueP` (§2.8), and the comparison matrix is a GUE matrix. The paper quotes this Remark (p. 9).

### 4.3 The two ways `L32` is weaker than [32, Theorem 2.2]

1. **Along size sequences.** `L32` is a statement for each size sequence, with the premises required for large
   `n` only and fixed `δ, σ, q, c, C, C_V, k, O`. [32, Theorem 2.2] gives, for these fixed parameters, one `C`
   and one `κ` for every `N`, `V`, `t`, `E` satisfying the premises (the standard reading of the theorem).
2. **The rate.** The bound `C N^{-κ}` is weakened to "tends to `0`".

### 4.4 The two places where `L32` is used

Both are in Step 1 of the proof of Theorem 2.6 (p. 9), the limit (18), with `t_* = N^{-1+τ_U}`.

1. **The band matrix.** Conditionally on `H`, `𝐇_{t_*}` is Dyson Brownian motion started from the diagonal
   matrix of the eigenvalues of `e^{-t_*/2}H − E`, run for time `1 − e^{-t_*} ∼ t_*`; [32] is applied at energy
   `0`. The initial data is `(g, G)`-regular with probability `1 − N^{-D}`, by the local law (Theorem 2.3). This
   is `RBM.Univ.step1Band`; the regularity and the closeness of the free-convolution density to `ρ_sc(E)` are
   `RBM.Univ.step1Good_highProb` (with `g = N^{-1+τ_U/4}`, `G = N^{-min(τ_U/4,(1−τ_U)/3)}`; the paper says
   `g = N^{-1+τ_U/2}`, `G = N^{-τ_U/8}`, "say").
2. **The translation of the GUE from energy 0 to energy `E`.** `𝐇_∞` has the law of `𝐇_{t_*}` started from an
   independent GUE matrix, and the same argument compares its statistics near `E` with those of the GUE near `0`
   (p. 9). This is `RBM.Univ.guetranslationRow`; the regularity premise comes from the GUE local law
   `RBM.Univ.gueLocal`, proved in Lean (the paper cites [26] for it).

---

## 5. Where the Lean proof takes a different route

None of the items below changes a statement of §1. For each item: the paper's step, the Lean replacement and
the main declarations. In `RBM2D/`, the directory `Propagator` corresponds to Lemma 2.14 and Section 8, `Loop`
to Section 3, `Green` to Section 4, `Path` to the discrete walk and Step 2 of Theorem 2.20 (Section 5.3),
`Induction` to the other steps of Theorem 2.20 (Sections 5.1 and 5.4–5.7), `Evolution` to Step 6 (Section 5.8)
and Section 7, `Universality` to the proof of Theorem 2.6, and `Main` to Theorems 2.2–2.6. Many deterministic lemmas are
proved with explicit constants where the paper writes `O(·)`, `≍` or `≺` (for example §5.6), and implicit
conditions (such as `|E| < 2 − κ`, `‖ξ‖ < 1`) are hypotheses.

### 5.1 The Brownian flow (pp. 11–12, 28)

- **Paper.** The matrix Brownian motion `dH_{t,xy} = √S_xy dB_{t,xy}`, `H_0 = 0`, the spectral parameter
  `z_t^{(E)} = E + (1 − t)m(E)` (Definition 2.7); the Itô formula for `G_t` and for the loops (Lemma 2.11,
  (35)–(37)); stopping times for `H_t` (Lemma 5.3, (105)).
- **Lean.** Two models with the paper's one-time laws.
  - `RBM.Gauss.Hflow u ω = √u · Xmat ω` (`d.seqHflow` on the sequence space): the right law at each time, not a
    Brownian path. It turns the identity in law (30) into a pointwise identity: `RBM.Endpoints.zGreen` says
    `G_X(z) = √u (H_u − z_u)^{-1}` for `H_u = √u X` and `(E, u) = (lemE z, lemT z)` (`RBM.lemE`, `RBM.lemT`);
    `RBM.Endpoints.zRange`, `zMeta`, `zAve`, `zTrace`, `zProfile` give the remaining parts of Lemma 2.8 and
    (55), (56).
  - `RBM.Path.pathH`: for a grid `u_k = s + kΔ`, `H_{u_k} = √s X_0 + √Δ Σ_{i=1}^k X_i` with independent copies
    `X_i` of the band matrix, on `RBM.Path.pathP` with the filtration `RBM.Path.filt`; `RBM.Path.transferLaw`
    says that its law at step `k` is the law of `d.seqHflow` at time `u_k`. Arguments that need several times
    (stopping times, martingale bounds) are carried out on this walk.

### 5.2 From the Itô formula to Gaussian integration by parts

- **Paper.** The drift of a loop is read off from the Itô formula (35)–(37).
- **Lean.** At one time, the derivative in `u` of an expected loop is the expectation of a finite sum of cut loops
  (`RBM.Gauss.deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts`); the second-order terms come from
  Stein's identity `E[x f(x)] = v E[f'(x)]` for each real coordinate (`RBM.integral_mul_gaussianReal`;
  `RBM.Gauss.GaussianProduct.stein` for the product law). The paper itself uses Gaussian integration by parts in
  Lemma 5.15 (Step 6, p. 46); in Lean `RBM.Evol.step61`. Along the walk, one Gaussian increment is expanded to
  second order in the matrix and first order in time: `RBM.Path.oneStepEnvelope` says that for Hermitian `M`,
  `|E| < 2`, `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1` and a loop of length `k`,
  `‖E Φ_{u+Δ}(M + √Δ X) − Φ_u(M) − Δ·genMat‖ ≤ envConst · Δ^{3/2}`, where
  `RBM.Path.genMat` is `½ Σ_c gvar_c ∂_c² Φ_u + ∂_u Φ_u`, the generator that the Itô formula produces. The grid
  has `K = max 1 ⌈N^{C_K}⌉` steps, `C_K = D_1 + 2D + 80` (`RBM.Path.gridK`), so the accumulated remainders are
  negligible; the conditional drift along the walk is `RBM.Path.condExp_loop_drift`.

### 5.3 Martingale terms: Azuma–Hoeffding and Chebyshev instead of BDG

- **Paper.** The martingale term of the stopped hierarchy (105) is bounded by the Burkholder–Davis–Gundy type
  inequality of Lemma 5.5 (108), quoted from [50].
- **Lean.** On the grid, the linear part of the one-step martingale increment is conditionally sub-Gaussian,
  and the stopped sum is bounded by the Azuma–Hoeffding inequality (`RBM.Path.azuma_two_sided`,
  `RBM.Path.azuma_complex`, `RBM.Path.stopped_duhamel_azuma_tail_fixed`, `RBM.Path.highProb_azuma_grid'`). The
  quadratic remainder is bounded by Chebyshev's inequality at the stopping index
  (`RBM.Path.stopped_duhamel_cheb_tail`).

### 5.4 Stopping times, nets, the iteration in time, and `≺`

- **Paper.** Stopping times for `H_t` (Lemma 5.3, p. 28; Step 2, pp. 29–32); uniformity in time "by a standard net
  argument" after (88) (p. 25) and "by another continuity argument" (Step 2, p. 32); Theorem 2.20 is iterated
  along the times `1 − s_k = W^{-kτ'}` (p. 19).
- **Lean.** Stopping times are first hitting indices of the grid: `RBM.Path.firstHit` (a stopping time:
  `RBM.Path.isStoppingTime_firstHit`) and `RBM.Path.gridTau`, the first `k` at which `RBM.Path.jStarMat` (the
  quantity `J*` of (111), (112)) reaches `RBM.Path.thr`, with the exit from the good set `RBM.Path.gridTauFull`.
  The stopping argument of Step 2 is `RBM.Path.gridStep2PT`, `RBM.Path.gridStep2Eq53PT`. The continuity
  estimate (88) is `RBM.Ind.gopbound`. Bounds uniform in time follow from bounds at each time by explicit
  polynomial nets (`RBM.Gauss.netSize`, `RBM.Gauss.netPt`, `RBM.Gauss.exists_netPt_close`) and a union bound.
  The passage from Theorem 2.20 and the initial data (57) to Lemmas 2.16–2.18 is `RBM.Ind.chainTarget`.
  The relation `≺` of Definition 2.1(i) (pp. 4–5) is `RBM.StochDomAt` along the dimensions `size n`, and
  `RBM.Path.PerTimeDomAt` is the per-time form, with the union over time outside the probability. Moment bounds
  (`RBM.Gauss.MomentDomAt`) give `≺` by Markov's inequality (`RBM.Gauss.stochDomAt_of_momentDomAt`); the reverse
  (`RBM.Gauss.momentDomAt_of_stochDomAt`) uses the whole-space bound `‖G(z)‖ ≤ (Im z)^{-1}`.

### 5.5 The loops `𝒦`

- **Paper.** `𝒦` is defined as the unique solution of (38) with the initial data (Definition 2.12, p. 15); the
  tree representation of [50, Lemma 3.4] is used in Section 3 (pp. 21–24).
- **Lean.** `RBM.KLoop.Kcal` is defined by the explicit tree sum over the crossing-free sets of diagonals of
  the polygon (`RBM.KLoop.TSP`), with (47) for `n = 2`. `RBM.KLoop.isPrimitive_Kcal` shows that it solves
  (38) with the initial data, and `RBM.KLoop.isPrimitive_eq_Kcal` that every solution on `[0, 1)` equals it. The
  Ward identity (72) is `RBM.KLoop.Kcal_ward`.

### 5.6 The propagator `Θ` (Lemma 2.14, Section 8)

- **Paper.** (42)–(44) with `≺`, for `ξ ∈ {tm², t m̄², t|m|²}`; Section 8 uses the periodic Euclidean norm,
  equivalent to the periodic `L¹` norm up to a factor `√2`.
- **Lean.** The periodic `L¹` distance `RBM.zdist2`, and explicit constants for every `‖ξ‖ < 1`:
  `RBM.norm_Theta_apply_le_prop5` gives
  `‖Θ_ξ(a,b)‖ ≤ 180·40002² (1 + log L)(κ²ℓ̂²)^{-1} exp(−|a − b|/(20000 ℓ̂))` with `κ = |1 − ξ|^{1/2}`,
  `ℓ̂ = min(κ^{-1}, L)` (`RBM.kappa`, `RBM.ellhat`), and `RBM.norm_Theta_fd_prop6` gives (43), (44) with the
  prefactor `8·10^{14} + 720(1 + log L)`. The factors `1 + log L` are absorbed by `≺`. The Fourier route of
  Section 8 is carried out in `RBM2D/Propagator`. For the oscillation of `Θ` there is also the bound
  `RBM.norm_Theta_sub_le_log`: `‖Θ_ξ(u,0) − Θ_ξ(v,0)‖ ≤ 90(1 + log L)` for all `‖ξ‖ < 1`.

### 5.7 Statements that the paper takes from the literature or omits, proved in Lean

| Paper | Lean |
|---|---|
| Proof of Theorem 2.2 "identical to that in [50], so we omit it" (p. 6) | `RBM.Endpoints.decol_of_locSC : locSC → decol` (§5.8) |
| Proof of Theorems 2.3 and 2.5 "the same argument as ... in [50]" (p. 18) | `RBM.Endpoints.locSC_QDiff_of_STOAll` |
| Lemma 2.8, "same as Lemma 2.7 in [50]" (p. 12) | `RBM.Endpoints.zGreen`, `zRange`, `zMeta` (§5.1) |
| Section 4, Lemma 4.1 "follows that of Lemma 4.1 in [50]" (p. 24) | `RBM.Green.gbEXPV3 : RBM.Green.GbEXPV3Theorem` |
| Lemma 5.1, "same argument as in Section 6 of [50]" (p. 26) | `RBM.Ind.conArg` |
| Lemmas 2.16–2.19 (p. 17), for every bulk energy sequence and time sequence in range; Lemma 5.15 (p. 46) | `RBM.Endpoints.p7Out_holds`, `RBM.Endpoints.p7ExpOut_holds`; `RBM.Evol.step61` |
| The claims on `𝐇_t` (p. 10): Theorem 2.4 for `𝐇_t`, and the diagonal entries of `R_t(z)` are `≺ 1`; "details identical to Section 7.2 of [50], so we omit them" | `RBM.Univ.OUQUE`, `RBM.Univ.OUDiag` (from `RBM.Univ.GUEPhase.g1Row`, `RBM.Univ.g2bRow`, `RBM.Univ.ouDiag_of_ouLL`) |
| "Standard calculations" [25, Theorem 15.3], [45, Proposition 4.17], [50, (2.23)] reducing (19) to the Claim (20) (p. 9) | `RBM.Univ.greenCorrAll` (Poisson smoothing of the test function, decomposition of sums over distinct indices) |
| (21), (22), (23): "argue as in Step 3 ... (2.28) in [50]", Lemma 4.20 of [45], "follow the proof of (2.29), (2.30) in [50]" (pp. 10–11) | `RBM.Univ.emcte2Row`, `RBM.Univ.jakRow`, `RBM.Univ.uywRow` |
| The GUE local law "(see e.g. [26])" (p. 9) | `RBM.Univ.gueLocal` |

`RBM.Univ.gueLocal` is proved from the Schur complement formula with a deterministic bootstrap
(`RBM.Univ.gueSchurTail`). The processes in (18)–(20) are used only through their one-time laws
`𝐇_t = e^{-t/2} H + √(1 − e^{-t}) H'` with `H'` an independent GUE matrix (`RBM.Univ.ouMat`, on the carrier
`RBM.Univ.ouP`); the generator identity for `E Φ(𝐇_t)` is `RBM.Univ.ouGenerator_hasDerivAt_integral`. The
matrix `𝐇_t` has the variance profile `(1 − ζ)S + ζN^{-1}J`, `ζ = 1 − e^{-t}`, and the Lean proofs of the
claims on `𝐇_t` use its propagator (`RBM.Univ.norm_ThetaTilde_sub_le`). The estimate (21) is proved in a
weighted form: the factors `∏ Im m_t(z_j)`, which the paper bounds by `N^{Cτ_U}` outside an event of
probability `O(N^{-D})` (p. 10), stay inside the expectation (`RBM.Univ.EMCTE2`, `RBM.Univ.Jak`,
`RBM.Univ.Uyw`).

### 5.8 The deductions of Theorems 2.2 and 2.4

- **Theorem 2.2** (`RBM.Endpoints.decol_of_locSC`). Apply Theorem 2.3 at the exponent `θ = min(τ, 𝔠, 1)/2` and
  `D + 2`, at the `4N + 1` points `E_j = min(2 − κ, −2 + κ + j/N)` and `η = N^{-1+θ}`. For an orthonormal
  eigenbasis, `|ψ_k(x)|² ≤ 2η Im G_xx(E_j + iη)` when `|μ_k − E_j| ≤ η`, and `|G_xx| ≤ |m| + 1 ≤ 2`; a union bound
  finishes. (No Lipschitz bound in the energy is needed.)
- **Theorem 2.4** (`RBM.Endpoints.QUE_of_QDiff`). Only the expectation half (12), (13) of Theorem 2.5 is used, at
  the exponent `min(𝔠, 1)/12` and `D = 1`, at the single spectral parameter `z = E + iη` with `η = W^{2/3}/N`
  (the paper takes `η = N^{-1-τ}W^{2/3}`, and `N^{-1-τ/2}W^{2/3}` for (9)); the window half-width is at most `η`.
  The differences of the profile `Θ` between blocks are bounded by `RBM.norm_Theta_sub_le_log` (§5.6) in place of
  the sum of (43) along a path of length `O(L)` (pp. 7–8); the factor `1 + log L` is absorbed by a power of `W`.
  Both (8) and (9) follow from Markov's inequality.

---

## Appendix A. The Lean statements

The five statements and the definitions they use (namespace `RBM.Endpoints`, file `RBM2D/Endpoints.lean`).
`ellz`, `Meta`, `Gn` are described in §2.7, `gueP`, `gueVar` in §2.8.

```lean
-- Theorem 2.2
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (μ : ι → ℝ) (ψ : ι → ι → ℂ) : Prop :=
  (∀ k k', star (ψ k) ⬝ᵥ ψ k' = if k = k' then 1 else 0) ∧
    ∀ k, H *ᵥ ψ k = (μ k : ℂ) • ψ k

def decolEvent (d : Sizes) (n : ℕ) (κ τ : ℝ) (ω : SeqΩ d) : Prop :=
  ∀ (μ : Idx (d.L n) (d.W n) → ℝ) (ψ : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ),
    IsOrthoEigenbasis (seqXmat d n ω) μ ψ →
      ∀ k, μ k ∈ Set.Icc (-2 + κ) (2 - κ) →
        ∀ x, ‖ψ k x‖ ^ 2 ≤ ((d.size n : ℕ) : ℝ) ^ (-1 + τ)

def decol : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop,
        seqP d {ω | ¬ decolEvent d n κ τ ω} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

-- Theorem 2.3
noncomputable def mSC (z : ℂ) : ℂ :=
  ∫ x in (-2 : ℝ)..2, ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ) / ((x : ℂ) - z)

def locDomain (N : ℕ) (κ τ : ℝ) (z : ℂ) : Prop :=
  |z.re| ≤ 2 - κ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 1

def locSC : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop, ∀ z : ℂ, locDomain (d.size n) κ τ z →
        -- (G_bound)
        seqP d {ω | ¬ ∀ x y : Idx (d.L n) (d.W n),
            ‖Gn d n ω z x y - (if x = y then mSC z else 0)‖ ≤
              (d.W n : ℝ) ^ τ / Real.sqrt (Meta (d.L n) (d.W n) z)} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) ∧
        -- (G_bound_ave)
        seqP d {ω | ¬ ∀ a : Z2 (d.L n),
            ‖((d.W n : ℂ) ^ 2)⁻¹ * ∑ x ∈ Iblk (d.L n) (d.W n) a, Gn d n ω z x x -
                mSC z‖ ≤
              (d.W n : ℝ) ^ τ / Meta (d.L n) (d.W n) z} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D))

-- Theorem 2.4
def window {ι : Type*} (N W : ℕ) (τ E : ℝ) (μ : ι → ℝ) (k : ι) : Prop :=
  |μ k - E| ≤ (N : ℝ) ^ (-1 - τ) * (W : ℝ) ^ ((2 : ℝ) / 3)

def queBad (d : Sizes) (n : ℕ) (τ E : ℝ) (a : Z2 (d.L n)) (ω : SeqΩ d) : Prop :=
  ∃ (μ : Idx (d.L n) (d.W n) → ℝ) (ψ : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ),
    IsOrthoEigenbasis (seqXmat d n ω) μ ψ ∧
      ∃ k k', window (d.size n) (d.W n) τ E μ k ∧
        window (d.size n) (d.W n) τ E μ k' ∧
        ((d.size n : ℕ) : ℝ) ^ (-τ / 6) ≤
          ‖((d.size n : ℕ) : ℂ) *
              (star (ψ k) ⬝ᵥ ((Epaper (d.L n) (d.W n) a -
                ((d.size n : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) *ᵥ ψ k'))‖ ^ 2

def que2Bad (d : Sizes) (n : ℕ) (τ E : ℝ) (A : Finset (Z2 (d.L n)))
    (ω : SeqΩ d) : Prop :=
  ∃ (μ : Idx (d.L n) (d.W n) → ℝ) (ψ : Idx (d.L n) (d.W n) → Idx (d.L n) (d.W n) → ℂ),
    IsOrthoEigenbasis (seqXmat d n ω) μ ψ ∧
      ∃ k, window (d.size n) (d.W n) τ E μ k ∧
        (A.card : ℝ) * (d.W n : ℝ) ^ 2 / ((d.size n : ℕ) : ℝ) ^ (1 + τ / 6) ≤
          |∑ a ∈ A, ∑ x ∈ Iblk (d.L n) (d.W n) a, ‖ψ k x‖ ^ 2 -
            (A.card : ℝ) * (d.W n : ℝ) ^ 2 / ((d.size n : ℕ) : ℝ)|

def QUE : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ τ : ℝ, 0 < τ → τ < 𝔠 / 2 → ∀ κ : ℝ, 0 < κ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| < 2 - κ →
        (∀ a : Z2 (d.L n),
          seqP d {ω | queBad d n τ E a ω} ≤
            ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-τ / 6))) ∧
        (∀ A : Finset (Z2 (d.L n)), A.Nonempty →
          seqP d {ω | que2Bad d n τ E A ω} ≤
            ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-τ / 6)))

-- Theorem 2.5
noncomputable def trGEGE (d : Sizes) (n : ℕ) (ω : SeqΩ d) (z : ℂ) (σ : Bool)
    (a b : Z2 (d.L n)) : ℂ :=
  Matrix.trace (Gn d n ω z * Epaper (d.L n) (d.W n) a *
    (if σ then Gn d n ω z else (Gn d n ω z)ᴴ) * Epaper (d.L n) (d.W n) b)

noncomputable def profile (L W : ℕ) [NeZero L] (z : ℂ) (σ : Bool)
    (a b : Z2 L) : ℂ :=
  let ξ : ℂ := if σ then mSC z ^ 2 else ((‖mSC z‖ ^ 2 : ℝ) : ℂ)
  ((W : ℂ) ^ 2)⁻¹ * (ξ * Theta L ξ a b)

def QDiff : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop, ∀ z : ℂ, locDomain (d.size n) κ τ z → ∀ σ : Bool,
        seqP d {ω | ¬ ∀ a b : Z2 (d.L n),
            ‖trGEGE d n ω z σ a b - profile (d.L n) (d.W n) z σ a b‖ ≤
              (d.W n : ℝ) ^ τ / Meta (d.L n) (d.W n) z ^ 2} ≤
          ENNReal.ofReal (((d.size n : ℕ) : ℝ) ^ (-D)) ∧
        ∀ a b : Z2 (d.L n),
          ‖(∫ ω, trGEGE d n ω z σ a b ∂(seqP d)) -
              profile (d.L n) (d.W n) z σ a b‖ ≤
            Meta (d.L n) (d.W n) z ^ (-(3 : ℤ)) * (d.W n : ℝ) ^ τ

-- Theorem 2.6
noncomputable def kPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) ^ k / ((Fintype.card ι).descFactorial k : ℝ)) *
    ∑ f : Fin k ↪ ι, O (fun j => (Fintype.card ι : ℝ) * (lam (f j) - E))

def BUniv : Prop :=
  ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ d : Sizes, Admissible 𝔠 d →
    ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ O : (Fin k → ℝ) → ℝ,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
          Tendsto (fun n =>
            (∫ ω, kPoint k O E (seqXmat_isHermitian d n ω).eigenvalues ∂(seqP d)) -
            (∫ ω, kPoint k O E (Xmat_isHermitian (d.L n) (d.W n) ω).eigenvalues
              ∂(gueP (d.L n) (d.W n))))
            atTop (𝓝 0)
```
