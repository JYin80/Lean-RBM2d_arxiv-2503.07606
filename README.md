# Lean formalization of Dubova–Yang–Yau–Yin, "Delocalization of two-dimensional random band matrices"

This repository contains a Lean 4 / Mathlib proof of the main results of

> Sofiia Dubova, Kevin Yang, Horng-Tzer Yau and Jun Yin, *Delocalization of two-dimensional random
> band matrices*, [arXiv:2503.07606](https://arxiv.org/abs/2503.07606).

The version of the paper that the Lean code follows is
[`paper/DubovaYangYauYin_RBM2D_Lean_version.pdf`](paper/DubovaYangYauYin_RBM2D_Lean_version.pdf)
(LaTeX source in `paper/tex/`). Page, equation and theorem numbers in `docs/PAPER-VS-LEAN.md` refer
to this PDF.

Sister project: [RBM1D](https://github.com/JYin80/Lean-RBM1d_arxiv-2501.01718), the Lean proof of
Yau–Yin, *Delocalization of one-dimensional random band matrices* (arXiv:2501.01718).

## Main results

The five statements are written in [`RBM2D/Endpoints.lean`](RBM2D/Endpoints.lean) as closed
propositions; the theorems are in [`RBM2D/Main/Endpoints.lean`](RBM2D/Main/Endpoints.lean) and
[`RBM2D/Main/BUnivHolds.lean`](RBM2D/Main/BUnivHolds.lean).

| Paper | Lean statement | Lean theorem | What it says |
|---|---|---|---|
| Theorem 2.2 | `RBM.Endpoints.decol` | `RBM.Endpoints.decol_holds` | Delocalization: with probability at least `1 − N^{−D}`, every eigenvector whose eigenvalue lies in `[−2+κ, 2−κ]` satisfies `‖ψ_k‖²_∞ ≤ N^{−1+τ}`. |
| Theorem 2.3 | `RBM.Endpoints.locSC` | `RBM.Endpoints.locSC_holds` | Local semicircle law: the entrywise bound (4) and the block-averaged bound (5), each with probability at least `1 − N^{−D}`, uniformly in `z = E + iη` with `\|E\| ≤ 2−κ`, `N^{−1+τ} ≤ η ≤ 1`. |
| Theorem 2.4 | `RBM.Endpoints.QUE` | `RBM.Endpoints.QUE_holds` | Generalized quantum unique ergodicity, (8) and (9), for `0 < τ < 𝔠/2` and `\|E\| < 2−κ`. |
| Theorem 2.5 | `RBM.Endpoints.QDiff` | `RBM.Endpoints.QDiff_holds` | Quantum diffusion, (10)–(13): high-probability and expectation bounds for `tr(G E_a G^† E_b)` and `tr(G E_a G E_b)` around `W^{−2} ξ Θ_ξ(a,b)`. |
| Theorem 2.6 | `RBM.Endpoints.BUniv` | `RBM.Endpoints.bUniv_holds` | Bulk universality, (17): at every energy with `\|E\| ≤ 2−κ`, the difference between the `k`-point correlation functions of the band matrix and of the GUE, rescaled around `E` and integrated against a smooth compactly supported test function, tends to 0. |

Theorems 2.2–2.5 have no hypotheses other than their parameters. Theorem 2.6 has one more
hypothesis, `RBM.Univ.L32`, described below. `docs/PAPER-VS-LEAN.md` lists every difference between
a Lean statement and the printed one (for example, the statements are made along any admissible
sequence of sizes, which is the paper's "there is `N₀` such that for all `N ≥ N₀`").

## The model and the one external input

The matrix is the complex Gaussian block band matrix of the paper's §2.1 on the torus `Z_L²`:
`L²` blocks of size `W × W`, `N = W²L²`, entries independent up to Hermitian symmetry, complex
Gaussian off the diagonal and real Gaussian on the diagonal, with variance profile
`S = S^{(B)} ⊗ S_W`, where `S^{(B)}_{ab} = 1/5` for blocks at periodic L¹-distance at most 1
(`L ≥ 3`) and `S_W` is the uniform `W² × W²` matrix, and with `W ≥ N^𝔠` for some `𝔠 > 0`.

The proof uses exactly one result from the literature without proving it: the fixed-energy
universality of Dyson Brownian motion, [32, Theorem 2.2] (B. Landon, P. Sosoe, H.-T. Yau, *Fixed
energy universality of Dyson Brownian motion*, Adv. Math. 346 (2019)), in the form stated in
[arXiv:1609.09011v4](https://arxiv.org/abs/1609.09011v4), whose Remark after Theorem 2.2 covers the
complex Hermitian case. It enters only Theorem 2.6, as the explicit hypothesis `RBM.Univ.L32`
(stated in `RBM2D/Universality/Pins.lean`). `docs/PAPER-VS-LEAN.md` states it and explains how it is
used.

## Axioms

Every declaration of the library depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry` and no declared `axiom`. The last command of `RBM2D.lean`,
`#assert_rbm_axioms` (defined in `RBM2D/Test/Axioms.lean`), checks this for every declaration in
the namespace `RBM`, and makes the build fail otherwise.

## Build

The toolchain is `leanprover/lean4:v4.34.0` (file `lean-toolchain`) with Mathlib `v4.34.0`.

```
lake exe cache get
lake build
```

`lake exe cache get` downloads the compiled Mathlib; `lake build` builds the whole library,
including the axiom check above.

The hypotheses of the five theorems can be satisfied: `RBM.Endpoints.admissible_witnessSizes`
exhibits an admissible size sequence (`L = n + 3`, `W = (n + 3)²`, `𝔠 = 1/3`), and
`RBM.Endpoints.locSC_holds_instance` and the examples in `RBM2D/Main/BUnivHolds.lean` apply the
theorems to it (the examples for Theorem 2.6 take `L32` as a hypothesis).

## Map of the library

- `RBM2D/Defs/`: the block variance profile and the block projections `E_a`, distances on `Z_L²`, the semicircle Stieltjes transform `m`, and stochastic domination `≺`.
- `RBM2D/Propagator/`: the propagator `Θ_ξ = (1 − ξS^{(B)})^{−1}` on `Z_L²` and Lemma 2.14: its Fourier representation and the Fourier-analytic proof of the decay, derivative and difference estimates (§8).
- `RBM2D/Loop/`: deterministic `G`-loops: the primitive loops `𝒦`, their tree representation, Ward's identity, the sum-zero property and the bounds on `𝒦^{(π)}` (§3).
- `RBM2D/Green/`: estimates for the entries of the Green's function, the minor formulas, large deviation estimates and fluctuation averaging (§4).
- `RBM2D/Gauss/`: the Gaussian band matrix on an explicit probability space, Gaussian integration by parts, and derivatives and continuity of loops along the flow.
- `RBM2D/Hierarchy/`: the loop hierarchy of §5: contractions of loops and the generator identity.
- `RBM2D/Path/`: the discrete time grid used in place of the matrix Brownian motion, stopping times, martingale bounds, and Step 2 of the proof of Theorem 2.20.
- `RBM2D/Evolution/`: the evolution kernel estimates of §7 and the related lattice sums.
- `RBM2D/Induction/`: the continuous induction over the time grid (Steps 1–6 of the proof of Theorem 2.20).
- `RBM2D/Universality/`: the proof of Theorem 2.6: the Ornstein–Uhlenbeck flow, the Green's function comparison, the free convolution, eigenvalue interlacing, the GUE local law and the GUE phase, and the statement of the external input `L32`.
- `RBM2D/Main/`: the assembly of Theorems 2.2–2.6 from the results above.
- `RBM2D/Endpoints.lean`: the five statements; `RBM2D/Delocalization.lean`: from a Green's function bound to eigenvector delocalization; `RBM2D/Test/Axioms.lean`: the axiom check.

## `docs/PAPER-VS-LEAN.md`

[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) compares the paper and the Lean proof in detail:
what is proved, every difference between the Lean statements and the printed ones, uniformity in
the sizes, the external input [32], and where the Lean proof takes a different route from the paper.

## License and authors

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE). The LaTeX class files
in `paper/tex/` (`imsart.cls`, `imsart.sty`, `imsart-number.bst`) are the IMS journal template by
VTeX, under the MIT license in `paper/tex/LICENSE-imsart`.

Paper: Sofiia Dubova, Kevin Yang, Horng-Tzer Yau and Jun Yin. Lean formalization: Jun Yin.
