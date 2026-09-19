# 形式化路线图（RBM2D）

## 项目形状（为什么是这个形状）

1. **Mathlib 没有随机分析**：没有 Itô 公式、矩阵布朗运动、SDE、Dyson Brownian motion。
   论文 §5–§7 的随机流（loop hierarchy、`ML:GLoop`、`lem:main_ind` 的归纳）**目前在 Lean 里无法证明**，
   只能作为 `axiom` 接口挂起来。
2. **可完全形式化的是确定性内核**：§2.5 的传播子 `Θ^(B)_ξ` + **§8 全部** + §3–4 的组合层。
   纯线性代数 / Fourier 分析 / 组合，且 §8 正是这篇论文相对 [YY_25] 必须重做的部分 ——
   d=1 的闭式解在 d=2 不存在。
3. 所以：**自下而上建确定性骨架，随机层留接口，§8 是主战场。**

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
| — | 随机层（Itô、loop hierarchy、`lem:main_ind`、universality） | — | **不形式化**，写成 `axiom` |

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
| 围道平移在 Lean 里成本失控 | 先做阶段 2（不需要围道），围道那块单独估时；实在不行退到 Combes–Thomas 型算子论证，代价是前因子差一个 `κ^{-2}`，**够不到论文的锐化常数**，只能当中间结果 |
| 显式常数 C、c 的追踪很痛 | 统一 `∃ C > 0, ∃ c > 0, ∀ ...`，不求最优；`≺` 用 `DetDom` 封装 |
| 范围蔓延 | 蓝图依赖图是唯一进度真相；Phase 1 不碰随机层任何东西 |

## 蓝图

`blueprint/src/content.tex` 写**整篇论文**的骨架（章节 + 每条定理的壳子和 `\uses{}`），
但只给已形式化的节点填 `\lean{}` 和 `\leanok`。依赖图配色：
绿 = 已形式化，蓝 = 已陈述未证，灰 = 仅在蓝图里（随机层）。
渲染需要 `pip install leanblueprint`，`leanblueprint web` 产出可推 GitHub Pages。
