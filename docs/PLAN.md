# 形式化路线图（RBM2D）

## 项目形状（为什么是这个形状）

1. **Mathlib 没有随机分析** —— 没有 Itô 公式、矩阵布朗运动、SDE、Dyson Brownian motion。
   **但这篇论文不需要它们。** 2026-09-20 的随机层审计（`docs/random-layer.md`）逐条核过：
   全文**没有**用到域流/适应性、Markov 性、两时刻联合律、Doob 不等式
   —— `filtration` 全文只出现一次，还只是 Lemma 5.5 假设里对停时 `T` 的量词修饰，证明里从不使用。
   所以 §5–§7 走 **d=1 的替代栈**：`H_u := √u·X` 一时刻边缘律 + 高斯分部积分（Stein）
   + 生成元恒等式 + 对矩的 Grönwall + 连续归纳（替代停时）+ 两座 `≺`⇄矩 的桥。
   论文自己就在用这个表示（`7:431`、式 (30)）。
2. **完全形式化的是确定性内核**：§2.5 的传播子 `Θ^(B)_ξ` + **§8 全部**。
   纯线性代数 / Fourier 分析，且 §8 正是这篇相对 [YY_25] 必须重做的部分 ——
   d=1 的闭式解在 d=2 不存在，这条捷径断掉，一开始就得上一般 Fourier 机器。
3. **永不写 `axiom`。** 做不了的写成 `structure` 字段或定理参数，等基础设施到位
   **原地换成定理、签名一个字不改**。`RBM2D.lean` 末尾的 `#assert_rbm_axioms`
   对整个 `RBM` 命名空间硬检查，**没有 allow-list**，违规即编译失败。
   范例：`Propagator/Dyadic.lean` 的 `DyadicDecomp`。
4. 所以：**自下而上建确定性骨架，§8 是主战场，随机层走替代栈而不是挂接口。**

## 阶段表

| 阶段 | 内容 | 依赖 | 状态 |
|---|---|---|---|
| 0 | 脚手架：lakefile、CI、`Z2 L` 索引层、`S^(B)`、`Θ`、性质 1–4、粗界、`≺`、谱论 | — | **草稿已写，未编译**（T1） |
| 1 | §8.1：`(eq_symbol)`、`(eq_Fourier_rep)`、`(eq_qdef)`、`(eq_qcomp)`、`(eq_elliptic)` | 0 | **完成**（T1 + T2 均已 CI 绿，0 sorry） |
| 2 | §8.2 的 **κL < 1** 区制 + §8.3 的 **Case 2**：只用椭圆性 + 格点求和 `Σ_{p≠0}|p|_*^{-2} ≲ L² log L` | 1 | 未开始（T14、T15、T16 可立刻开工 → T3 → T4 ∥ T5） |
| 3 | §8.2 的 **κL ≥ 1** 区制：无穷体积核 `(eq_Kinf)`、围道平移 `(eq_shifted_lower)`、`(eq_Kinf_bound)`、Poisson 求和 | 1 | 未开始（T7–T9），**最硬** |
| 4 | §8.3 的 Case 1：dyadic 分解 `(eq_dyadic)` 与两个求和 `(eq_dyadic_sum1/2)` | 3 | 未开始（T10） |
| 5 | §2 的模型层：`S = S^(B) ⊗ S_W` on `Z_{WL}^2`、`I^(2)_a`、`E_a`、`(deri_Thxi)` | 0 | 未开始（T5、T6） |
| 6 | §3–4 的组合层（loop 指标、cut-and-glue、树表示） | 5 | 未开始，**等 §8 落地后再排** |
| 7 | **随机层替代栈**：`Defs/StochDom.lean`、Stein 三层、生成元恒等式、两座桥、对矩的 Grönwall、连续归纳、卸掉 (108) 与停时 | 5 | **已开工**：S1（确定性包络 `‖G‖ ≤ η⁻¹`）完成；S0/S2/S3/S8 可立刻并行 |
| — | §3–§4 的平面组合几何（典范划分 ↔ 无交叉配对） | — | **不形式化**，按论文结论取用。高维「无交叉」不是同一个概念，形式化代价与收益不成比例 |

### 为什么把阶段 2 排在阶段 3 前面

论文 §8.2 的两个区制难度天差地别：

- `κL ≥ 1`（`ℓ̂ = κ⁻¹`）：需要无穷体积核、Cauchy 定理做围道平移、Poisson 求和。
- `κL < 1`（`ℓ̂ = L`）：**只需要把零模单独拎出来**，其余模用椭圆性，
  再加一条 `Σ_{p ∈ T_L²\{0}} |p|_*^{-2} ≤ C L² log L`。三行纸、Lean 里大概一天。

§8.3 的 Case 2（`|s|_L > d/2`）同理，也只用椭圆性。
先把这两块做掉，`lem_propTH` 的性质 5、6 就各有一半是定理而不是猜想了，
而且 `Σ_{p≠0}|p|_*^{-2}` 这条格点求和引理在阶段 3、4 里还会反复用到。

### 阶段 3 的关键风险

Mathlib 里**有**围道所需的零件，但得先确认签名：

- 矩形围道：`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`（名字待 grep 确认）
- Poisson 求和：`Real.tsum_eq_tsum_fourierIntegral` 一族（同上）

**但本项目其实可以绕开 Poisson 求和**：论文自己说了
「by Poisson summation, **or simply by comparing Fourier coefficients** in
`(eq_Fourier_rep)` and `(eq_Kinf)`」。在 Lean 里，后者是把
`K_{ξ,L}(x) = Σ_n K_{ξ,∞}(x + nL)` 化归为「两个函数的 Fourier 系数相同」，
比调用 Poisson 求和定理的解析假设更容易。**优先走这条**（见 T9）。

## Phase 1（= 阶段 0–2）完成标准

1. `./check.sh` → 零 error、零 sorry
2. `#print axioms` 对每条主定理只出现 `propext / Classical.choice / Quot.sound`
3. `lem_propTH` 的性质 1–4 全部是定理；性质 5 在 `κL < 1` 区制、性质 6 在 `|s|_L > d/2`
   情形是定理
4. `leanblueprint checkdecls && leanblueprint web` 通过
5. 人工复核 PDF §8（`paper/tex/8_theta_properties.tex`），特别确认
   `ℓ̂(ξ) = min(|1−ξ|^{−1/2}, L)` 的定义与 `(prop:ThfadC)` 分母上的 `|1−ξ|·ℓ̂(ξ)²`

## 风险与对策

| 风险 | 对策 |
|---|---|
| Cowork 写的第一批文件编不过 | T1 就是干这个的；错基本集中在 Mathlib 引理名与 `simp` 副目标 |
| Mathlib 版本 API 漂移 | 锁死 `v4.34.0`；不确定的名字先 grep 或 `#check` |
| `Prod` 上的 `Finset` 记账（五点支撑集的互异性） | 全部集中在 `Defs/Block.lean` 的 `card_sbSupport` / `sum_over_sbSupport` 两条，改一处即可 |
| 围道平移在 Lean 里成本失控 | 先做阶段 2（不需要围道）。**Combes–Thomas 已单独立为 T29**：它能独立结清性质 5 的两个 ξ（`|1−ξ| ≥ c`，正是 §3–§4 实际消费的区制），但衰减率退化到 `κ²`，`1/L ≤ κ ≪ 1` 仍然要围道，**不能替代 T27+T28** |
| 显式常数 C、c 的追踪很痛 | 统一 `∃ C > 0, ∃ c > 0, ∀ ...`，不求最优；`≺` 用 `DetDom` 封装 |
| 范围蔓延 | 蓝图依赖图是唯一进度真相。随机层已进范围，但**只走替代栈那 11 个文件**，不造随机分析 |

## 蓝图

`blueprint/src/content.tex` 写**整篇论文**的骨架（章节 + 每条定理的壳子和 `\uses{}`），
但只给已形式化的节点填 `\lean{}` 和 `\leanok`。依赖图配色：
绿 = 已形式化，蓝 = 依赖就绪可开工，白 = 尚被上游阻塞，橙 = 不形式化（取论文结论）。
渲染需要 `pip install leanblueprint`，`leanblueprint web` 产出可推 GitHub Pages。
