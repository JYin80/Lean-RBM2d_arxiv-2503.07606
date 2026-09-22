# 进度（对照论文编号）

论文：`paper/2503.07606-aop-submission.pdf`（AOP 提交版，68 页），源码在 `paper/tex/`。
工具链：Lean 4.34.0 / Mathlib v4.34.0。构建：macOS 本机，`./check.sh` → `build.log`。

---

## 当前摘要（2026-09-22 05:41 UTC；以下旧条目是历史日志）

- **范围**：按 `docs/PLAN.md` 推进整篇 d=2 论文；§8 的确定性传播子与
  §3–7 的随机层替代路线都在范围内。
- **基线**：主分支 `5d40557` 起步，Lean 4.34.0。两个仓库的十个依赖 commit
  逐项一致；当前环境无法解析 GitHub 域名，故从 RBM1D 的本机缓存建立了
  独立 copy-on-write 副本。`./check.sh` 全量通过：3446 jobs、errors 0，
  `#assert_rbm_axioms` 报告 392 个 `RBM` 声明，仅使用
  `propext`、`Classical.choice`、`Quot.sound`。
- **非阻塞维护项**：构建有 10 条 linter warning，位于 `Defs/Dist.lean` 与
  `Gauss/Envelope.lean`；旧表中“T13 后全仓 0 warning”已过时。
- **在飞工单**：S4（一时刻高斯模型）在原有独立工作树；T19（dyadic cutoff）
  与 T25（二维对数积分）在当前对话内代理中；T23 的条件版、
  T3、T7、S0、S2、T4、T5 和 S3 的乘积高斯核心已集成。
  不再新建项目对话条。
  协调任务持有共享文档与蓝图。
  T3 原规格的 `3/π²`
  与现有粗壳层界不直接相符，
  已改为可由已证引理推出的 `4/π²`。原文所说 `CL³` 足够 T5 亦已更正。
- **蓝图**：已补 §2–4 的 loop/卷积树、局部律、QUE、量子扩散以及
  Bulk universality 的完整主定理骨架；`[YY_25]` 及短时 OU/DBM 外部输入
  单列开放节点。S3 乘积高斯核心与实际矩阵实例化分开标记。当前静态检查
  73 节点、113 个已有声明引用均有效；
  本机 XeLaTeX 生成 12 页 PDF，此机缺 `dot`。
- **下一轮解锁**：T7 → S4；T3 → T4/T5；S0 → S2/S3/S5 的前置链。
  新单以实际声明和编译探针核对，不能仅靠旧工单状态。
- **T3 集成（2026-09-22 05:15 UTC）**：`LatticeSum.lean` 证明了
  `sum_inv_pstar2_le`（显式 `4/π²`）、归一化对数界与
  `normalizedPuncturedSum_detDom_one`；`L=3` 的非空正和例子已编译。
  主分支全量 `./check.sh` 通过：3447 jobs、errors 0，公理审计覆盖
  413 个 `RBM` 声明，仅有标准三项公理。蓝图 T3 节点对应的三个声明
  已经静态核对，T4、T5 的格点和前置已解除；具体下游陈述仍须各自编译。
- **T7/S0 集成（2026-09-22）**：`Model.lean` 将论文的
  $S=S^{(B)}\otimes S_W$、$Z_{WL}^2$ 分块、$E_a$、行和及自伴性连通；
  `StochDom.lean` 将 Def. 2.1(i)(iii)(iv) 的坏事件、范数版与高概率事件
  写成随机量定义，证明闭包、并集界和 $L$ 尺度 `UnifDetDom` 到允许的
  $N(L)=W(L)^2L^2$ 尺度的单向桥。两份模块有正的非平凡例子，无
  `sorry`、新增公理或可任意赋值的证明字段。主分支 `./check.sh` 全量通过：
  3449 jobs、errors 0；公理审计覆盖 548 个 `RBM` 声明，只用标准三项。
  Blueprint 的 T7/S0 节点已标绿；静态检查 50 节点、99 个声明引用均有效。
  S0 以同一个样本空间/概率测度承载不同 $N$ 的随机量，这与论文按维数
  叙述的分布族等价地使用时，后续 S4 需检查共同概率空间的具体构造。
- **Blueprint CI 修复（2026-09-22）**：上一轮文档生成在
  `content.tex` 原第 389 行的未定义 `\Z` 命令停下；同章还有
  `\Z_{WL}` 和 `\E` 未在蓝图宏文件中定义。已改用现有 `\ZL` 与
  标准 `\mathbb Z`、`\mathbb E`。本机 XeLaTeX 已完整产出 11 页 PDF，
  后续以推送后的 CI 再核对网页版与发布。
- **S2 集成（2026-09-22）**：`Stein.lean` 从高斯密度导数证明实值
  Stein 恒等式，再由实虚部分解证明复值测试函数版；有单位方差下
  `sin` 的非平凡探针。`./check.sh` 全量通过：3595 jobs、errors 0，
  公理审计 580 个 `RBM` 声明仅用标准三项。Blueprint 将原 S2/S3
  合并节点拆为标绿的标量 S2 与仍开放的矩阵 S3；现有 51 节点、103
  个声明引用，XeLaTeX 完整生成 11 页 PDF。
- **T4 集成（2026-09-22）**：`Decay.lean` 在 $\kappa L<1$ 下证明
  $\hat\ell=L$、零模与格点和的显式界、带指数因子的
  `norm_Theta_apply_le_small_kappa_log`，并证明归一化前因子 `≺1`。
  $L=3,\xi=35/36$ 是非空区制探针。主分支 `./check.sh` 全量通过：
  3596 jobs、errors 0；公理审计 597 个 `RBM` 声明仍只用标准三项。
  Blueprint T4 节点标绿；静态检查 51 节点、106 个声明引用。
- **S3/T5 集成（2026-09-22）**：`SteinMatrix.lean` 对可数实高斯坐标积测度
  证明重采样不变与复值 Stein 恒等式，覆盖零方差，有单位方差非平凡测试；
  实际 Hermitian 矩阵实例化待 S4。`FiniteDiff.lean` 证明 §8.3 Case 2
  两条论文尺度的有限差分界，公共显式系数 $720(1+\log L)\prec1$，
  并验证 $L=3,\xi=0,u=0,s=(1,0)$ 非空。主分支全量 `./check.sh`
  通过：3666 jobs、errors 0；629 个 `RBM` 声明只用标准三项公理。
  Blueprint 对通用定理与 Case 2 标绿，矩阵接口与总性质 6 仍开放。
- **T23 条件版（2026-09-22）**：`DerivBounds.lean` 合并 Case 1/Case 2，
  将两条论文尺度推广到任意矩阵指标，证明若 `DyadicDecomp` 的常数
  `H.C≤C₀`，则公共系数 $8C₀+720(1+\log L)\prec1$。
  这是清晰的 T22 接口，**不是**无条件 Property 6；T22 必须构造
  `DyadicDecomp` 并给出统一的 `C₀`。全量 `./check.sh` 通过：3667 jobs、
  errors 0；648 个 `RBM` 声明只用标准三项公理。蓝图静态检查通过。

---

# 历史日志：三个杠杆（2026-09-19 晚；以顶部当前摘要为准）

进度确实偏慢，原因诊断如下，**按影响排序**。这一段是给 Claude Code 和心跳两边看的。

### 1. 现在就开 Claude Code 做队列 —— 唯一的数量级差别

队列里现在有 **6 条**可立刻开工、文件两两不相交的工单
（**T6、T7、T8、T13、T15、T17**）。T2、T16 已完成，T14 已由 Cowork 认领并写完草稿。
到 11:55 为止这 6 条**一条都没人动** —— 这仍然是唯一的数量级差别。

Cowork 侧编译不了 Lean（云端出口挡掉 Mathlib 的 olean cache，设备 VM 没有 Lean），
它的回路是「写 → push → 读 CI 日志 → 改」，一轮 5 分钟起步，T1 那一批走了 6 轮。
Claude Code 在本机 `lake env lean 单文件` 是**秒级**，而且自己能 push。
同一件事两边的成本差两个数量级 —— **凡是 Claude Code 能做的，都不该由 Cowork 做。**

Cowork 侧应当做的是：规划、开工单、读论文、维护蓝图、以及 CI 红了没人管时兜底。

### 2. 同时开两个 Claude Code 实例

**T6**（`Propagator/Deriv.lean`）、**T7**（`Defs/Model.lean`）、**T8**（`Test/Numeric.lean`）、
**T15**（`Propagator/Shells.lean`）、**T17**（`Propagator/GeomSum.lean`）五条文件互斥、互不依赖
（T14、T16 已由 Cowork 取走）。工单表里那条「一条工单独占一个文件」的规矩就是为这个写的：
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

## 2026-09-19 11:55 UTC：T14 草稿落地 + 队列补回 6 条（Cowork 心跳）

CI：`Lean Action CI #24`（`727c14c`）**Success**。开工前 `git status` 干净、与 `origin/main` 同步，
**没有未推的旧提交** —— 上一轮的四个本地提交都已由本机侧推上去了，回路没有卡。

### 为什么这一轮取 T14 而不是 T15

上一节把 T15 点名留给了本机侧（纯 `Finset` 记账，副目标形状要试几次，秒级迭代占便宜两个数量级）。
45 分钟过去 T15 仍然空闲，但**抢过来是错的** —— 抢了它 Cowork 要走 5 轮 CI，本机侧 5 分钟。
链上的另一条是 **T14**（`Propagator/ZeroMode.lean`）：它是代数改写，一次写对的概率高，
正是 CI 回路擅长的那类。而且 T14 和 T15 文件互斥，两边可以真的并行。
**T15 仍然留给本机侧，优先级不变。**

### 写了 T14 的 `RBM2D/Propagator/ZeroMode.lean`（**未编译，按草稿对待**）

落地 8 个声明，0 sorry：

| 声明 | 内容 |
|---|---|
| `Shat_zero` | `Ŝ(0) = 1`（五项都是 1） |
| `chr_zero_left` | `e_0(u) = 1` |
| `one_sub_mul_Shat_zero` | `1 − ξŜ(0) = 1 − ξ` |
| `norm_chr` | `‖e_p(u)‖ = 1` |
| `norm_chr_div_one_sub_mul_Shat` | 单项的模就是 `‖1 − ξŜ(p)‖⁻¹` |
| `norm_chr_sub_le` | `‖e_p(u) − e_p(v)‖ ≤ 2`（T5 的 Case 2 要的粗界） |
| **`Theta_apply_eq_zero_mode_add`** | **§8.2 的零模分离**，T4 的第 1 步 |
| **`Theta_apply_sub_eq_erase_sum`** | **§8.3 的零模消失**，T5 的第 1 步 |

后三条是工单里没要求、但 T4/T5 立刻要用的配套，放这里省得两边各写一遍。

### 这份草稿里不确定的地方（CI 这一轮要盯的）

Mathlib 名字全部在 `../RBM1D/.lake/packages/mathlib/`（同 rev）里逐条 grep 核对过：
`AddChar.map_zero_eq_one`（`Algebra/Group/AddChar.lean:111`，`@[simp]`）、
`Circle.norm_coe`（`Analysis/Complex/Circle.lean:74`，`@[simp]`）、
`ZMod.stdAddChar_apply`（`Symbol.lean` 里已经在用）、
`Finset.add_sum_erase`（`prod_erase` 那族的 `to_additive`，方向是
`f a + ∑_{s.erase a} = ∑_s`，所以要 `.symm`）、`Finset.sum_sub_distrib`（`@[simp]`）、
`Prod.fst_zero` / `Prod.snd_zero`。**按上一轮的教训，四个模块全部显式 import 了一行。**

| 位置 | 风险 |
|---|---|
| `norm_chr` 的 `exact Circle.norm_coe _` | `stdAddChar_apply` 的 RHS 用的是哪个 `Circle → ℂ` 陪域可能与 `Circle.norm_coe` 不同形。报 type mismatch 就换 `simp [chr, ZMod.stdAddChar_apply]`（两条都是 `@[simp]`） |
| `Shat_zero` 收尾的 `norm_num` | 若前面的 `simp only` 自己就把 `(1+(1+1)+(1+1))/5` 算成 `1`，`norm_num` 会报 "no goals"。删掉即可 |
| `Theta_apply_eq_zero_mode_add` 的 `hsplit` | `Finset.add_sum_erase` 的 `f 0` 是 λ 应用，靠 `have` 的 defeq β-归约吃掉；T16 那一轮同样的写法过了 |
| `Theta_apply_sub_eq_erase_sum` 收尾的 `ring` | 要把两个 `∑` 当原子。`simp only [sub_div, Finset.sum_sub_distrib]` 之后两边的求和必须逐字同形；不同形就先 `rw [Finset.sum_congr rfl ...]` 显式对齐 |

### 蓝图

`lem:zero-mode` 补了 `\lean{}`（`render_artifact.py` 的 checkdecls 过了，5 个名字确实存在），
**故意没给 `\leanok`**。新增节点 `lem:dyadic-sums`（T17，见下）。
现在 32 个节点：`done 11 / defn 8 / ready 5 / blocked 6 / cited 2`，163 条 Lean 声明、0 sorry。
蓝图工件已就地更新（v9）。

### 队列：补了 T17，仍是 6 条

认领 T14 之后空闲只剩 5 条，所以补了一条 **T17**（`Propagator/GeomSum.lean`）：
`(eq_dyadic_sum1)` 与 `(eq_dyadic_sum2)`，论文 `8_theta_properties.tex` 第 177–178 行。

`TASKS.md` 原文自己写过「这两条是纯算术，可以先于 `(eq_dyadic)` 单独做掉」。
这一轮把它兑现成有自己文件的工单，价值在于**它把 T11 的风险切成两半**：
即使 `(eq_dyadic)` 那条逐环估计卡死、被迫降级成引用接口（见本文件开头第 3 条杠杆），
这两条求和也已经是定理。工单里把两次劈开（`r ∼ κ`、`r ∼ (d+1)^{-1}`）写全了，
并核对出 **`M = 3` 对两条都够**，不需要论文的「`M` 任意大」。

空闲且文件两两不相交：**T6、T7、T8、T13、T15、T17**。

### 给对面的话

- `ZeroMode.lean` 第一件事是拿到本机编译，别当定理用。
- **T15 仍然是唯一在关键路径上的空闲工单，请优先做它。** T2、T16 已完成，
  T15 一落地 T3 就只剩组装；T3 一通，T4 与 T5 就都能并行开工，而它们的另一个前置 T14
  这一轮已经有草稿了。
- T17 是新的，纯实数算术，和 T15 一样适合本机秒级迭代，但**不在关键路径上**。
- 本轮新增 4 个本地提交，仍需本机 `git push`。

---

## 2026-09-19 11:03 UTC：**T16 完成**（CI #22 绿，一轮过）

`Lean Action CI #22`（`a29ec0b`）**Success**，`lake build exit 0`、3434 jobs、0 error、
`Harmonic.lean` **一条 warning 都没有**。上一节那张「不确定的地方」表里的四条，
**一条都没触发** —— `simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, ...]` 的方向对了，
两处 `calc` 的 β-归约靠 `exact` 的 defeq 吃掉了，`nlinarith` 的提示也够。

连续两轮（T2 的 `Momentum.lean`、T16 的 `Harmonic.lean`）都是**导入改对之后一轮过**，
这支持 CI 第 1 轮得出的那条结论：**Cowork 侧写 Lean 的真实失败模式是作用域，不是战术。**
凡是从 Mathlib 深处取引理，就把它所在的模块显式 import 一行，代价是一行，收益是一整轮 CI。

`lem:harmonic` 已补 `\leanok`（语句 + 证明各一处）。蓝图现在 31 个节点：
`done 11 / defn 8 / ready 4 / blocked 6 / cited 2`，155 条 Lean 声明、0 sorry。
蓝图工件已就地更新（v6）。

### 队列：7 条 → 6 条，但关键路径只剩一条

空闲且文件两两不相交：**T6、T7、T8、T13、T14、T15**。

**T15（`Propagator/Shells.lean`）是唯一在关键路径上的那条。**
T2 和 T16 都完成了，所以 `lem:latticesum`（T3）现在**只差 T15**；
T3 一通，T4 与 T5 就都能并行开工，`lem_propTH` 的性质 5 和性质 6 就各有一半变成定理。
T6/T7/T8/T13 是叶子，随时可做，但做完不解锁任何东西。

**给对面的话**：如果只开一个 Claude Code 实例，请先做 T15。
它全程在 ℕ 和 `Finset` 里，一个实数都不出现，正是本机秒级迭代最占便宜的那类活
（`Finset.card_union_le` / `Finset.filter_product` 的副目标要试几次形状）。

---

## 2026-09-19 11:00 UTC：T16 草稿落地（Cowork 心跳）

CI：`Lean Action CI #18`（`78f2459`）**Success**，`lake build exit 0`、3396 jobs、0 error。
`Momentum.lean` 完整编过了 —— 上一节那张「不确定的地方」表里的四条战术风险
**一条都没有触发**，`field_simp`/`linarith`/`nlinarith` 全部按预期走通。
唯一残留是 `Momentum.lean:242` 的 `<;>` 风格警告，已由本机侧在 `d2923b7` 清掉。

`Compile blueprint #10/#11` 之前红过，根因同样是 `Momentum.lean`
（该 workflow 的 `Build project` 步骤就是 `lake build`），随 `#18` 一起自愈，**不是独立问题**。

### 写了 T16 的 `RBM2D/Propagator/Harmonic.lean`（**未编译，按草稿对待**）

队列 7 条、CI 绿，所以这一轮仍按分工规矩取链上的那条而不是叶子：
T16 → T3 → T4/T5。落地 4 个声明，0 sorry：

| 声明 | 内容 |
|---|---|
| `mul_log_le_rpow` | `τ · log x ≤ x^τ`（`x > 0`，τ 任意） |
| `sum_inv_Icc_le_one_add_log` | `Σ_{k∈[1,n]} 1/k ≤ 1 + log n`，ℝ 版 |
| `one_add_log_detDom_one` | `1 + log L ≺ 1` |
| `harmonic_detDom_one` | `Σ_{k∈[1,L]} 1/k ≺ 1` ← **T3 最后一步要的就是这条** |

另加两条非负性小引理（`sum_inv_Icc_nonneg`、`one_add_log_nonneg`），
因为 `DetDom` 的闭包引理都把「被控量非负」写成显式假设。

**工单里有一处写错了，已绕开**：T16 第 4 步说用 `DetDom.mono_left`。
`Defs/Domination.lean` 里**没有** `DetDom.mono_left`，只有 `UnifDetDom.mono_left`。
草稿改走 `detDom_iff` 展开后 `filter_upwards`，不依赖任何 `mono_left`。

**一个刻意的选择**：第 2 步写成乘法形式 `τ · log x ≤ x^τ`，而不是工单里的
`log x ≤ x^τ / τ`。这样全文件**一个除法引理都不需要** —— `le_div_iff₀` /
`div_le_div_of_nonneg_right` 这一族正是跨 Mathlib 版本最容易改名的。
我在 pinned 源码里 grep `le_div_iff₀` 确实没找到，绕开是对的。

### 这份草稿里不确定的地方（CI 这一轮要盯的）

所有 Mathlib 名字都在 `../RBM1D/.lake/packages/mathlib/`（同 rev）里逐条 grep 核对过：
`harmonic_eq_sum_Icc`、`harmonic_le_one_add_log`、`Real.log_le_sub_one_of_pos`、
`Real.log_rpow`、`Real.rpow_pos_of_pos`、`Real.log_natCast_nonneg`、
`inv_div`、`eventually_ge_atTop`、`le_of_mul_le_mul_left`（`(a*b ≤ a*c) → 0 < a → b ≤ c`）。
风险在战术不在名字：

| 位置 | 风险 |
|---|---|
| `sum_inv_Icc_le_one_add_log` 的 `simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]` | 这三条 cast 引理是从 Mathlib 自己那条证明里**逐字抄**的 `simp_rw` 行，但我这里是 `simpa ... using h`，方向相反。不过就改成 `rw` 再 `exact` |
| 收尾两处 `calc` 的最后一步 `_ = (L:ℝ)^τ * 1` | 目标里 `f`、`g` 还是 λ 形式没 β 归约，靠 `exact` 的 defeq 吃掉。若报 type mismatch，就在 `filter_upwards` 后加一句 `simp only []` 或 `show` |
| `hmain` 里的 `nlinarith [mul_le_mul_of_nonneg_right hstep hA.le]` | 提示给够了应该纯线性（单项式 `τ·A²`、`τ·A`、`A` 当原子），真不行就换 `linarith` 同一个提示 |
| `Harmonic.lean` 的 import | 显式加了 `Log/Basic` 与 `Pow/Real` 两行，就是为了不再重犯 CI 第 1 轮的作用域错 |

### 蓝图

`lem:harmonic` 补了 `\lean{}`（`render_artifact.py` 的 checkdecls 过了，4 个名字确实存在），
**故意没给 `\leanok`** —— 没过 CI 就说「已形式化」是假的。

顺带补了一个真正缺的节点：**`def:detdom`**。`Defs/Domination.lean` 从 T1 起就是绿的，
但蓝图里**一个节点都没有**，依赖图一直在少算。现在 31 个节点：
`done 10 / defn 8 / ready 5 / blocked 6 / cited 2`。

### 给对面的话

- `Harmonic.lean` 第一件事是拿到本机编译，别当定理用。
- 队列仍是 7 条可立刻开工（T6、T7、T8、T13、T14、T15 + T16 已被 Cowork 认领 → 实际 6 条空闲），
  文件两两不相交。**T15 建议优先**：它和 T16 一起就解锁 T3，T3 一通 T4/T5 就都能并行开。
- 本轮新增 3 个本地提交，仍需本机 `git push`。

---

## 2026-09-19 10:50 UTC：**T2 完成**（CI 绿）+ 队列补到 7 条（Cowork 心跳）

CI：`Lean Action CI #12`（`2b5d11a`）**Success**。开工前 `git status` 干净、与 `origin/main` 同步。

### 写了 T2 的 `RBM2D/Propagator/Momentum.lean`（**未编译，按草稿对待**）

队列已经够深、CI 是绿的，所以这一轮按分工规矩取了**最深的那条**（T2 是
T2→T3→T4 串行链的链头；T6/T7/T8/T13 短平快，留给本机秒级迭代的 Claude Code）。

落地的声明：`pstar`、`pstar2`、`cos_eq_cos_pstar`、`pstar_le_pi`、
`pstar_pos_of_ne_zero`、`pstar2_pos_of_ne_zero`、`one_sub_cos_le_sq`、
`sq_le_one_sub_cos`、`qsym_le_pstar2`、`pstar2_le_qsym`、
`four_div_le_one_div_nine`、`norm_one_sub_mul_Shat_le_pstar`、
`norm_one_sub_mul_Shat_ge_pstar`。0 sorry。已加进 `RBM2D.lean` 的 import 列表。

**一个意外的便宜**：工单里写的「Jordan 不等式 + 半角公式」这条路**不用走**。
pinned Mathlib 的 `Analysis/SpecialFunctions/Trigonometric/Bounds.lean` 里直接有

```
Real.one_sub_sq_div_two_le_cos : 1 - x ^ 2 / 2 ≤ cos x            -- 无假设
Real.cos_le_one_sub_mul_cos_sq (hx : |x| ≤ π) : cos x ≤ 1 - 2 / π ^ 2 * x ^ 2
```

合起来就是 `(2/π²)θ² ≤ 1 - cos θ ≤ θ²/2`，一个半角都不用推。
（第二条的名字里的 `cos_sq` 有误导性，它讲的是 `x^2` 不是 `cos x ^ 2`。）

### 这份草稿里**不确定的地方**（CI 第一轮要盯的就是这几处）

所有 Mathlib 名字都在 `../RBM1D/.lake/packages/mathlib/Mathlib/`（同 rev `v4.34.0`）
里逐条 grep 核对过，**没有一个是猜的**。真正的风险在战术，不在名字：

| 位置 | 风险 |
|---|---|
| `cos_eq_cos_pstar` 的 `hval` | `field_simp [hLne] <;> ring`。用 `<;>` 是防 `field_simp` 自己关掉目标后 `ring` 报 "no goals"。若 `field_simp` 留下的形状 `ring` 收不掉，就手动 `rw [sub_div]` 再拆 |
| `pstar2_le_qsym` 的 `key` | 同上。这一步存在的唯一理由是 `linarith` 把 `π` 当原子，必须让它**逐字**看到 `2/π^2 * (pstar ·)^2` 这个整体，不能指望它自己除以 `π²` |
| `pstar_le_pi` 收尾的 `nlinarith [Real.pi_pos]` | 要 `π·(1-t) ≥ 0`，hint 不够就把 `h0`、`h1` 再显式喂一遍 |
| `simp only [qsym, pstar2]` 之后的 `linarith` | 依赖 `qsym` 里的 `2 * Real.pi * ↑p.1.val / ↑L` 和我的引理逐字同形。cast 若被 `simp` 归一成别的样子就对不上，改用 `rw [qsym]` 或显式 `show` |

**蓝图侧故意没有给 `lem:qcomp` 加 `\leanok`** —— 没过 CI 就说「已形式化」是假的。
`\lean{}` 标签加了（`render_artifact.py` 的 checkdecls 过了，说明这 6 个名字确实存在于源码里）。

### CI 第一轮的结果：错的不是上面那四条，是 import（已修）

`Lean Action CI #14/#15/#16` 红。三条 error，全是同一个毛病：

```
Unknown constant `Real.one_sub_sq_div_two_le_cos`
Unknown constant `Real.cos_le_one_sub_mul_cos_sq`
Unknown constant `Real.pi_gt_three`
```

三个名字**确实存在**（我在 `../RBM1D/.lake/packages/mathlib/` 里逐条 grep 过），
但 `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean` 与
`Mathlib/Analysis/Real/Pi/Bounds.lean` **不在 `Defs.Dist` + `Propagator.Elliptic`
的 import 闭包里**，所以不在作用域。

> **教训，值得写进 `CLAUDE.md`：grep 源码只能证明名字存在，不能证明它被 import 了。**
> 「不许发明 Mathlib 引理名」这条规矩防住了名字，没防住作用域。
> 从 Mathlib 深处取引理时，**同时把它所在的模块显式 import 一行**。

已在 `b39a47f` 修：显式加了那两个 import。顺带按同一份日志修掉了
`cos_eq_cos_pstar` 里 field_simp 之后多余的 `ring`、两处应当用 `;` 而非 `<;>` 的
field_simp、弃用的 `push_neg`、以及 `pstar2_nonneg` 的 `omit [NeZero L] in`。

上面那张「不确定的地方」表里的四条战术风险，**第一轮一条都没触发**
（错误全集中在 import），但它们在这一轮里也还没被真正执行到 —— `Momentum.lean`
在 `Unknown constant` 之后就没往下编了。

### CI 第二轮：绿。**T2 完成。**

`Lean Action CI #18`（`78f2459`）**Success，`lake build` exit 0**。
`Momentum.lean` 整份文件里只剩一条风格警告（`<;>` 应作 `;`），已在 `d2923b7` 修掉。

那四条战术风险**全部一次通过**，没有一条需要改：`field_simp` 的两处、
`pstar_le_pi` 的 `nlinarith`、以及 `simp only [qsym, pstar2]` 之后的 `linarith`
（说明 cast 的形状确实对得上）。

蓝图：`def:pstar` 与 `lem:qcomp` 已补 `\leanok`（语句 + 证明），节点统计
从 15 已形式化 / 6 可开工 变成 **17 已形式化 / 5 可开工**，工件已就地更新。

`lem_propTH` 性质 5、6 的前置里，**`(eq_qcomp)` 这一格从此是定理不是猜想**。
T3 现在只差 T15、T16 两条（都可立刻开工）。

### 队列：4 条 → 7 条

原来 T3 是一条「什么都干」的大工单，而 T4 和 T5 的第一步**是同一条引理**
（从 `(eq_Fourier_rep)` 里摘零模）—— 那两条工单其实并不文件互斥。拆成：

| 新工单 | 文件 | 从哪拆出来的 |
|---|---|---|
| **T14** 零模分离 | `Propagator/ZeroMode.lean` | T4 步骤 1 = T5 步骤 1，提出来只证一次 |
| **T15** `max`-壳层计数 | `Propagator/Shells.lean` | T3 的 Finset 记账（全程不碰实数） |
| **T16** 调和和 → `≺` 的桥 | `Propagator/Harmonic.lean` | T3 的另一半；Mathlib 的 `NumberTheory/Harmonic/Bounds.lean` 已经有 `harmonic_le_one_add_log` |

三条都只依赖已经绿的代码，**今天就能开工，且顺序随意**。

### 给对面的话

- `Momentum.lean` **第一件事是拿到本机编译**，别当定理用。
- T14/T15/T16 的工单里凡是写「已核对存在」的 Mathlib 名字，是真在 pinned 源码里 grep 过的；
  写「先 grep 确认」的（`Circle.norm_coe`、`Nat.max_eq_zero_iff`）是没核对的，别当真。
- 本地提交仍然要靠 Mac 这边 `git push`：Cowork 侧没有凭据。本轮新增 4 个本地提交。

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
