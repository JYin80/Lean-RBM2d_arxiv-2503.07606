# 已核实的 Mathlib 名字

**规矩**：不许发明 Mathlib 引理名。用过并且**编译通过**的记进「确认存在」；
`grep` 或编译确认**不存在 / 已改名**的记进「确认不存在」——后者同样值钱，
它省掉下一个人重复试错。

每条注明第一次用它的文件。Mathlib rev `5ed2965256`，Lean `4.34.0`。

## 确认存在（本仓已编译通过）

| 名字 | 用途 | 首次使用 |
|---|---|---|
| `min_choice` | `min a b = a ∨ min a b = b`，把 `zdist` 变成纯 ℕ 让 `omega` 收尾 | `Shells.lean` |
| `Finset.card_union_le` | `#(s ∪ t) ≤ #s + #t` | `Shells.lean` |
| `Finset.card_image_le` | `#(s.image f) ≤ #s` | `Shells.lean` |
| `Finset.card_insert_le` | `#(insert a s) ≤ #s + 1` | `Shells.lean` |
| `Finset.sum_fiberwise_of_maps_to` | 分层求和；**与 `Finset.sum_fiberwise` 签名不同，别拿错** | `Shells.lean` |
| `Finset.sum_image` | 高阶合一会失败，要**显式写出等式再 `rw`**，不能直接 `rw [← Finset.sum_image h]` | `GeomSum.lean` |
| `Finset.sum_le_sum_of_subset_of_nonneg` | 子集求和 | `GeomSum.lean` |
| `Finset.sum_filter_add_sum_filter_not` | 按谓词劈开求和 | `GeomSum.lean` |
| `Finset.sum_sub_distrib` | `∑(f−g) = ∑f − ∑g` | `Dyadic.lean` |
| `sum_geometric_two_le` | `∑_{i<n} (1/2)^i ≤ 2` | `GeomSum.lean` |
| `geom_sum_eq` | `∑_{i<n} x^i = (x^n−1)/(x−1)`，要 `x ≠ 1` | `GeomSum.lean` |
| `pow_le_of_le_one` | `0 ≤ a → a ≤ 1 → n ≠ 0 → a^n ≤ a` | `GeomSum.lean` |
| `pow_le_one₀` / `one_le_pow₀` | 底数在 `[0,1]` / `≥ 1` | `GeomSum.lean` |
| `pow_le_pow_of_le_one` | 底数 `[0,1]`，指数越大越小 | `GeomSum.lean` |
| `pow_le_pow_left₀` | `0 ≤ a → a ≤ b → a^n ≤ b^n` | `GeomSum.lean` |
| `one_div_le_one_div_of_le` | `0 < a → a ≤ b → 1/b ≤ 1/a`（配 `simpa [one_div]`） | `GeomSum.lean` |
| `inv_le_one₀` | `0 < a → (a⁻¹ ≤ 1 ↔ 1 ≤ a)` | `GeomSum.lean` |
| `inv_le_comm₀` | `0 < a → 0 < b → (a⁻¹ ≤ b ↔ b⁻¹ ≤ a)` | `GeomSum.lean` |
| `inv_anti₀` | `0 < a → a ≤ b → b⁻¹ ≤ a⁻¹` | `Dyadic.lean` |
| `div_le_iff₀` | `0 < c → (a/c ≤ b ↔ a ≤ b*c)` | `GeomSum.lean` |
| `norm_sum_le` | 三角不等式 | `Dyadic.lean` |
| `ZMod.natCast_val` + `ZMod.cast_id` | `((u.val : ℕ) : ZMod L) = u`，本仓包成 `RBM.natCast_val_self` | `Dist.lean` |
| `ZMod.val_lt` | 要 `[NeZero L]` | `Dist.lean` |
| `ZMod.neg_val` | 配 `ite_eq_right` | `Dist.lean` |
| `fwdDiff`、`fwdDiff_iter_eq_sum_shift` | `M := Z2 L`、`G := ℂ` 直接可用 | 待 T20 |
| `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` | 矩形 Cauchy，**一元就够** | 待 T27 |
| `Complex.cos_add_mul_I` | `cos(x+yI)` 展开，就是论文那一行 | 待 T27 |
| `Function.Periodic.intervalIntegral_add_eq` | **实变量版**，复方向竖边抵消不能用它 | 待 T27 |
| `Complex.norm_exp_I_mul_ofReal_sub_one` | `‖exp(Ix)−1‖ = ‖2 sin(x/2)‖`，**恒等式** | 待 T20 |
| `Real.mul_abs_le_abs_sin` | Jordan，要 `|x| ≤ π/2` | 待 T20 |
| `Matrix.l2_opNorm_mul` / `_mulVec` / `_def` | scoped 实例在 `Matrix.Norms.L2Operator` | 待 T29 |

## 确认不存在 / 已改名（**别写**）

| 写了会挂的 | 实际情况 |
|---|---|
| `le_or_lt` | 用 `lt_or_ge` |
| `inv_le_inv_of_le` | 没了。用 `inv_anti₀`，或 `one_div_le_one_div_of_le` + `simpa [one_div]` |
| `div_le_div_iff` | 没了。用 `rw [← sub_nonneg]` + `field_simp` + `div_nonneg` 绕 |
| `if_neg` | **已弃用**，换 `ite_eq_right` |
| `Complex.norm_exp_I_mul_ofReal_sub_one_le` | 在 **`Real`** 命名空间，不是 `Complex` |
| `Finset.sum_range_by_parts` 用于 `ZMod L` | 它只吃 ℕ-区间；`ZMod` 上要自己用 `Equiv.addRight` 写 |
| Mathlib 里的 Littlewood–Paley / dyadic 分解 | `grep -rli littlewoodpaley Mathlib` = 0 个文件 |
| `ContDiffBump` 的 `iteratedFDeriv` 定量界 | **整个 `BumpFunction/` 目录里没有**。这是 `(eq_dyadic)` 唯一真正的 Mathlib 缺口，T19 用显式 smoothstep 绕开 |
| 二维 Poisson 求和 / 二维 Fourier 反演 | 只有一维。T28 走逆的唯一性，整条绕开 |
| 有限交换群 / `ZMod` 上的 Abel 求和 | 没有 |

## `positivity` / `omega` 的边界（踩过的）

- **`positivity` 看不见假设**。`0 < dyad j`、`0 < kappa ξ ^ 2 + dyad j ^ 2` 这类要
  **先证成 `have` 再显式传**（`pow_nonneg (dyad_pos j).le 3`、`inv_nonneg.mpr …`），
  写 `by positivity` 会失败。
- **`omega` 看得见 `min` / `max`**，但**看不见没被 `simp` 成功改写的假设**。
  `simp only [Finset.mem_filter] at hp` 可能**静默不触发**（linter 会说 "This simp argument
  is unused"），于是 `omega` 拿到的是集合成员关系而不是等式。**用 `Finset.mem_filter.mp hp`
  显式取**，别靠 `simp`。
- `field_simp` 经常**自己就收尾了**，后面再跟 `ring` 会报 "No goals to be solved"。

## 语法坑

- `omit [NeZero L] in` 必须放在 **doc comment 之前**，放在 doc comment 和 `theorem`
  之间会 parse 错（`unexpected token 'omit'; expected 'lemma'`）。
- graphviz 在 SVG 的 `<title>` 里把 `-` 写成 `&#45;`（蓝图脚本踩过）。
- 本仓 `ellhat` 的签名是 **`ellhat L ξ`**，不是 `ellhat ξ L`。
