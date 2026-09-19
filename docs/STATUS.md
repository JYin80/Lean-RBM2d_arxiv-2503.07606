# 进度（对照论文编号）

论文：`paper/2503.07606-aop-submission.pdf`（AOP 提交版，68 页），源码在 `paper/tex/`。
工具链：Lean 4.34.0 / Mathlib v4.34.0。构建：macOS 本机，`./check.sh` → `build.log`。

---

# 下一步：三个杠杆（2026-09-19 晚，先读这一段）

进度确实偏慢，原因诊断如下，**按影响排序**。这一段是给 Claude Code 和心跳两边看的。

### 1. 现在就开 Claude Code 做队列 —— 唯一的数量级差别

队列里有 5 条可开工的工单（**T13、T6、T7、T8、T2**），到目前为止**一条都没人动**。

Cowork 侧编译不了 Lean（云端出口挡掉 Mathlib 的 olean cache，设备 VM 没有 Lean），
它的回路是「写 → push → 读 CI 日志 → 改」，一轮 5 分钟起步，T1 那一批走了 6 轮。
Claude Code 在本机 `lake env lean 单文件` 是**秒级**，而且自己能 push。
同一件事两边的成本差两个数量级 —— **凡是 Claude Code 能做的，都不该由 Cowork 做。**

Cowork 侧应当做的是：规划、开工单、读论文、维护蓝图、以及 CI 红了没人管时兜底。

### 2. 同时开两个 Claude Code 实例

**T6**（`Propagator/Deriv.lean`）、**T7**（`Defs/Model.lean`）、**T8**（`Test/Numeric.lean`）
三条文件互斥、互不依赖。工单表里那条「一条工单独占一个文件」的规矩就是为这个写的：
两个实例同时跑不会冲突，合并永远是平凡的。T13 只动 `Defs/Dist.lean` 等已有文件，
和这三条也不冲突，但它会碰别人正在读的文件，**建议先做完 T13 再并行**。

### 3. §8.3 的 dyadic 那块可能要降级 —— 这是范围决定，等撞上再说

26 个蓝图节点里 15 个绿了，但没绿的 11 个包含**真正重要的两个**：
`propTH-5` 和 `propTH-6`，也就是 §8 的全部内容。§8.1 是初等的，§8.2/§8.3 不是：

| 缺口 | 难度评估 |
|---|---|
| 二维格点求和 `Σ_{p≠0}\|p\|_*^{-2} ≤ CL²log L`（T3） | 中等，纯 Finset 记账 |
| Jordan 不等式 → `q ≍ \|p\|²_*`（T2） | 低，Mathlib 有 `Real.mul_le_sin` 一族 |
| 带参数的单复变围道平移（T9） | 高，但 Mathlib 有 `integral_boundary_rect_eq_zero_*` |
| 周期化（T10） | 中，**走比较 Fourier 系数，不要调 Poisson 求和定理** |
| **离散 Littlewood–Paley dyadic 分解 + 分部求和（T11）** | **最高。Mathlib 没有现成的，这是全项目唯一按周算的一块** |

如果 T11 卡死，备选是把 `(eq_dyadic)` 当作论文引用的既成结论挂成接口，
在 `docs/paper-deltas.md` 里把代价写清楚，换性质 6 的其余部分先落地。
**这是范围决定，需要 Jun 拍板，不要自行降级。**

---

## 2026-09-19：项目开张（Cowork 侧）

仓库从空目录建起。`RBM1D` 的工作约定（`CLAUDE.md` / `PLAN.md` / `TASKS.md` /
`paper-deltas.md` / `check.sh` / `watch.sh` / CI）全部沿用，数学路线另起 —— 见 `PLAN.md`
的「与 d=1 的根本区别」。

### ✅ 2026-09-19 晚：T1 完成，全部编译通过

`lake build` **exit 0**，10 个文件全绿，`grep -rn sorry RBM2D/` 为空。
CI: `Lean Action CI #7`（commit `8d27204`）Success。

修复过程（全部由 Cowork 侧通过读 CI 日志完成，共 5 轮）：

| 轮次 | 文件 | 问题 |
|---|---|---|
| 1 | — | 缺 `lake-manifest.json`，`lean-action` 在解析依赖前就退出 |
| 2 | `Defs/Block` | `zero_ne_neg_one_zmod` 的 `linear_combination` 系数写成了 `-h`，应为 `h` |
| 3 | — | 加了把 `lake build` 输出写进 `$GITHUB_STEP_SUMMARY` 的步骤（GitHub 不展开就只渲染前 40 行日志） |
| 4 | `Propagator/Symbol` | `stdAddChar_add_neg` 从 RBM1D 的 `Shat_eq_cos` 拆出来后，`rw [h]` 自己就关掉了目标，尾巴上的 `ring` 没活干 |
| 5 | `Propagator/Elliptic` | `le_or_lt` 在这版 Mathlib 里没了（用 `lt_or_ge`）；`simpa` 把 `\|1−lam\| = 1−lam` 经 `abs_eq_self` 化成 `lam ≤ 1`，对不上关于 ℂ 上范数的目标 |
| 6 | `Propagator/Elliptic` | `simp` 在 `((1 - lam : ℝ) : ℂ)` 上会先把 cast 往里推，推完就看不出参数是实数 —— 抽成对裸变量陈述的 `norm_ofReal_aux` 再 `rw` |

**一个意外收获**：linter 指出 `norm_one_sub_mul_real_le` 根本没用到 `‖ξ‖ < 1`。
确实如此 —— `(eq_elliptic)` 的**上界**只是三角不等式，对任意 `ξ` 都成立，
只有下界需要 `Re(1−ξ) > 0`。假设已删掉，记进 `paper-deltas.md` 第 9 条。

### 剩下的警告（不挡编译，见 TASKS.md 的 T13）

`Defs/Dist` 的 5 条 `show` 风格提示与 2 条 `if_neg` 弃用，
以及 7 处没用上的 section 变量 `[NeZero L]`。

### 蓝图

`blueprint/src/content.tex` 里 15 个带 `\lean{}` 的节点全部补上了 `\leanok`
（语句 + 证明各一处，共 29 个标记），41 个 `\lean{}` 标签逐一核对过都解析得到真实声明。
没有 `\lean{}` 的节点就是 `TASKS.md` 里还没开工的工单。

---

### ⚠️ 历史记录：第一批草稿的状态（已过时）

**下面列的所有 Lean 文件都是 Cowork 侧写的草稿，一行都没有编译过。**
Cowork 所在的云端容器拉不到 Mathlib 的 olean cache（出口策略挡掉了
`lakecache.blob.core.windows.net`），从源码编 Mathlib 在那边不现实。
所以这批文件的状态是「**已写，未验证**」，不是「已完成」。

**第一件事是 `docs/TASKS.md` 的 T1：在本机 `lake exe cache get` + `lake build`，
把它们编译通过。** T1 里列了每个文件的已知高风险点。

### 已写（未编译）

#### `RBM2D/Defs/Block.lean` — §2.1 的 `S^(B)` on `Z_L^2`

| Lean | 论文 |
|---|---|
| `RBM.Z2 L` | 索引类型 `Z_L^2`，实现为 `ZMod L × ZMod L` |
| `RBM.sbSupport` / `RBM.sbKernel` / `RBM.SB` | `S^(B)_{ab} = (1/5)·1(\|a-b\|_L ≤ 1)`，实现为 `Matrix.circulant` |
| `RBM.card_sbSupport` | `3 ≤ L` 时五个格点互异（论文隐含假设，见 paper-deltas #1） |
| `RBM.SB_isSymm` / `SB_transpose` | `lem_propTH` (1) 在 `S^(B)` 层面 |
| `RBM.SB_apply_add_right` | `lem_propTH` (2) 在 `S^(B)` 层面 |
| `RBM.sum_SB_row` / `RBM.SB_mulVec_one` | `S^(B)` 是随机矩阵 |

#### `RBM2D/Defs/Dist.lean` — §8 的 `|x|_L`

`RBM.zdist`（`ZMod L` 上的图距离，`RBM1D` 的逐字复制）、
`RBM.zdist2`（周期 L¹ 范数，见 paper-deltas #2）、三角不等式、
`RBM.SB_apply_eq_zero`（带宽结构）。

#### `RBM2D/Propagator/Basic.lean` — `def_Theta` + `lem_propTH` (1)–(4)

| Lean | 论文 |
|---|---|
| `RBM.norm_SB` | `‖S^(B)‖ = 1`（ℓ^∞ 算子范数） |
| `RBM.Theta` | `def_Thxi`，`Θ^(B)_ξ = (1 - ξ S^(B))⁻¹` |
| `RBM.Theta_mul` / `mul_Theta` / `eq_Theta_of_mul` | 双边逆与唯一性（下面几条都靠它） |
| `RBM.Theta_transpose` / `Theta_isSymm` | **性质 1** 对称 |
| `RBM.Theta_apply_add_right` | **性质 2** 平移不变 |
| `RBM.Theta_commute_SB` / `Theta_commute` | **性质 3** 可交换 |
| `RBM.Theta_eq_tsum` | **性质 4** `(theta_rw)` 随机游走表示 |
| `RBM.sum_Theta_row` | `Σ_b (Θ_ξ)_{ab} = (1-ξ)⁻¹`（§3–4 反复用） |

#### `RBM2D/Propagator/Bounds.lean` — 粗界

`RBM.norm_Theta_le`、`sum_norm_Theta_row_le`、`norm_Theta_apply_le`：
`≤ (1 - ‖ξ‖)⁻¹`。**这不是论文要的锐化界** —— 论文要的是由 `\|1-ξ\|` 而非 `1-\|ξ\|`
控制的 `ℓ̂(ξ) = min(\|1-ξ\|^{-1/2}, L)`，两者在 `ξ = tm²` 区制差别巨大。锐化界是 §8 的全部内容。

#### `RBM2D/Propagator/Symbol.lean` — §8.1 的 Fourier 建立

| Lean | 论文 |
|---|---|
| `RBM.Shat` / `Shat_eq_cos` | `(eq_symbol)`，`Ŝ(p) = (1 + 2cos p₁ + 2cos p₂)/5` |
| `RBM.chr` + 四条平移引理 | 平面波 `e_p(x) = exp(i p·x)` |
| `RBM.norm_Shat_le_one` / `one_sub_mul_Shat_ne_zero` | `‖ξ‖ < 1 ⟹ 1 - ξŜ(p) ≠ 0` |
| `RBM.SB_mulVec_apply` / `SB_mulVec_char` | `S^(B) e_p = Ŝ(p) e_p` |
| `RBM.inv_mul_sum_stdAddChar` / `inv_mul_sum_chr` | 特征标正交性（1 维 + 2 维） |
| **`RBM.Theta_apply_fourier`** | **`(eq_Fourier_rep)`** |

#### `RBM2D/Propagator/Elliptic.lean` — §8.1 的椭圆性

| Lean | 论文 |
|---|---|
| `RBM.kappa` / `RBM.ellhat` | `(eq_kappa_def)`，`κ = \|1-ξ\|^{1/2}`、`ℓ̂ = min(κ⁻¹, L)` |
| `RBM.kappa_sq` / `kappa_pos` / `kappa_mul_ellhat_le_one` | `κ² = \|1-ξ\|`、`κℓ̂ ≤ 1`（§8.3 要用） |
| `RBM.qsym` / `qsym_nonneg` / `qsym_le` | `(eq_qdef)`，`q(p) ∈ [0, 8/5]` |
| `RBM.Shat_eq_one_sub_qsym` | `Ŝ(p) = 1 - q(p)`，特别地 `Ŝ` 是实的 |
| **`RBM.norm_one_sub_mul_Shat_le` / `norm_one_sub_mul_Shat_ge`** | **`(eq_elliptic)`** 的上下两半 |
| `RBM.norm_one_sub_mul_Shat_ge_kappa` | 用 `κ²` 改写的版本，§8.2 直接用 |

论文在 `λ ≤ 1/2` 那一支写的常数 `1/2` 按字面不成立（应为 `2/5`），见 paper-deltas #5。

#### `RBM2D/Defs/Domination.lean` — `stoch_domination` (ii)

`RBM1D` 的逐字复制，只改了文件头：序列参数取 `L` 而非 `N`（见 paper-deltas #3）。

#### `RBM2D/Delocalization.lean` — `MR:decol` 的确定性核

`RBM1D` 的逐字复制（该文件对维度和带状结构完全无关）。
`RBM.green`、`green_eq_spectral`、`im_green_apply_self`、
**`sq_norm_eigenvector_le_im_green`**、`sq_norm_eigenvector_le_of_norm_green_le`。

---

## 下一步

见 `docs/TASKS.md`。顺序：**T1（编译）** → T6 ∥ T7 ∥ T8 → T2 → T3 → T4 ∥ T5。

`lem_propTH` 六条性质的状态：

| 性质 | 状态 |
|---|---|
| 1 对称 | 已写（`Theta_transpose`） |
| 2 平移不变 | 已写（`Theta_apply_add_right`） |
| 3 可交换 | 已写（`Theta_commute_SB` / `Theta_commute`） |
| 4 随机游走表示 | 已写（`Theta_eq_tsum`） |
| 5 指数衰减 `(prop:ThfadC)` | `κL < 1` 区制 = T4；`κL ≥ 1` 区制 = T9 + T10 |
| 6 导数界 `(prop:BD1)(prop:BD2)` | Case 2 = T5；Case 1 = T11 |

---

## 卡住的事情 / 给对面的话

- **Cowork 侧编不了 Lean。** 见上。所有「Cowork 写好了」都应读作「Cowork 写了草稿」。
- `lake exe cache get` 在本机第一次会拉几个 GB。`../RBM1D/.lake/packages` 已有一份
  同 rev 的 Mathlib，理论上可以共用，但**没有验证过 lake 会不会写坏那边的树**，
  不确定就老实 `cache get`。

---

## 环境小坑：`.git/_stale/`

这个仓库的第一批提交是从 Cowork 侧做的，那边的文件桥**不允许删除文件**，
于是 `git` 每跑一次写操作就会留下一个 0 字节的 `.git/index.lock` 和一堆
`.git/objects/**/tmp_obj_*`。我把它们挪进了 `.git/_stale/`（65 个文件），
这样 git 能正常用。

**在 Mac 上直接 `rm -rf .git/_stale` 即可**，里面没有任何有用的东西。
之后在本机跑 git 就不会再有这个问题（本机 git 权限正常）。

## CI 第一次跑：`lake-manifest.json` 缺失（已修）

第一次 push 之后 `Lean Action CI` 16 秒就红了，原因不是 Lean 代码，而是
**`No lake-manifest.json found`** —— `lean-action` 在解析依赖之前就退出了。

已从 RBM1D 复制一份（同 toolchain、同两条 require，解析出来的依赖集一致，
只有 `name` 字段不同），mathlib 锁在 `5ed2965256`。这同时也是**共用
`../RBM1D/.lake/packages` 的前提**：两边 rev 必须完全一致。

`Compile blueprint` 那条在建分支的那次 push 上没有触发（`paths` 过滤器在新建分支时
的行为），下一次 push 会带上它。

### 顺带发现：**CI 可以当 Cowork 的编译器**

GitHub runner 拉得到 olean cache，所以 `lake build` 的完整报错会出现在 CI 日志里。
Cowork 侧的回路因此是「写 → push → 读 CI 日志 → 改」，一轮约 10 分钟。
本机单文件编译是秒级，高频试错仍然归 Claude Code；CI 回路的用处是让 Cowork
写完的草稿不至于原封不动丢给对面 debug。

## 还没做的两件事（需要在本机 / 需要 Jun 决定）

1. **`git push`**：Cowork 侧没有 GitHub 凭据，所以只提交到了本地。
   远端已设好：`origin = https://github.com/JYin80/Lean-RBM2d_arxiv-2503.07606.git`，
   分支 `main`。在 Mac 上 `git push -u origin main` 即可。
2. **GitHub Pages**：仓库 Settings → Pages → Source 选 **GitHub Actions**。
   开完并 push 之后，站点在
   `https://jyin80.github.io/Lean-RBM2d_arxiv-2503.07606/`。
