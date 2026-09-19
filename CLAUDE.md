# CLAUDE.md — RBM2D

用 Lean 4 + Mathlib 形式化二维随机带状矩阵论文（arXiv:2503.07606，AOP 提交版）的确定性内核。

姊妹项目：`../RBM1D`（d=1，arXiv:2501.01718）。**很多写法可以照抄那边**，但数学路线不同，见下。

## 唯一真相来源

- **论文**：`paper/2503.07606-aop-submission.pdf`（68 页），源码在 `paper/tex/`。
  **只依据这篇论文，不引用任何其他文献**（论文里引 `[YY_25]` 的地方，在 Lean 里当作假设或另开工单，不要去读 d=1 的论文来补证明）。
- **路线图**：`docs/PLAN.md`
- **当前进度**：`docs/STATUS.md` —— **每次会话开始先读它，结束前更新它**
- **工单队列**：`docs/TASKS.md` —— **开工前先在表里认领并单独提交这一行**
- **与论文的偏差**：`docs/paper-deltas.md` —— 凡 Lean 陈述 ≠ 论文字面陈述，必须在这里记一条

## 与 d=1 的根本区别（这决定了整个项目的形状）

d=1 时最近邻三项递推有特征方程，闭式解 `(Θ_ξ)_{xy} = A(ξ)(ρ^d + ρ^{L−d})` 存在，
`RBM1D` 的衰减估计全部建立在它上面。**`Z_L^2` 上没有这种递推，闭式解不存在。**

所以 d=2 只有一条路：**§8 的 Fourier 路线**。
`Propagator/Symbol.lean`（Fourier 表示）和 `Propagator/Elliptic.lean`（椭圆性）
在 RBM1D 里是可选的结构性结果，在这里是**承重墙**。

§8 的四层结构，也就是 Phase 1 的四层：

1. **§8.1 Fourier 建立 + 椭圆性** `|1 − ξŜ(p)| ∼ κ² + |p|²_*` —— 纯初等，已写（待编译）
2. **§8.2 衰减 `(prop:ThfadC)`** —— 围道平移 + Poisson 求和。**最硬的一块**
3. **§8.3 导数界 `(prop:BD1)(prop:BD2)`** —— 动量的 dyadic 分解
4. 其中 **κL < 1 区制**（§8.2 后半）和**导数界 Case 2** 只用椭圆性，不需要围道平移，
   难度与第 1 层相当，应当早做 —— 见 `docs/TASKS.md` 的 T3、T4

## 环境

Lean `4.34.0` / Mathlib `v4.34.0`。仓库刚建，**`.lake/` 还没有**：

```bash
cd ~/Lean_proof/RBM2D
lake exe cache get      # 拉 Mathlib 预编译 olean（第一次会久）
lake build
```

`../RBM1D` 已有一份同版本的 Mathlib（`.lake/packages/mathlib/.lake/build` 约 6.6 GB）。
如果 `cache get` 太慢，可以考虑把 `RBM2D/.lake/packages` 做成指向 `../RBM1D/.lake/packages`
的符号链接 —— toolchain 与 rev 完全锁死一致，**但请先确认 `lake` 不会写坏那边的树**，
不确定就老老实实 `cache get`。

Mathlib 源码在 `.lake/packages/mathlib/Mathlib/` —— 找 API 就 grep 这里。

## 构建回路

```bash
lake env lean RBM2D/Propagator/Xxx.lean   # 单文件，秒级 —— 默认用这个
./check.sh                                 # 全量，结果写进 build.log
./watch.sh                                 # 另开终端，改动即自动重编
```

**绝不在没有实际跑过编译的情况下说「写好了」。** 每次回报前必须有一次 exit=0。

## 硬性规则

1. **不留 `sorry`。** 证不出来就停下说「卡在 X」，不要 sorry 占位然后继续往下写。
2. **不许发明 Mathlib 引理名。** 先 `grep -rn "circulant_mul" .lake/packages/mathlib/Mathlib/`，
   或新建一个临时 `RBM2D/Probe.lean` 加 `#check @foo` 编译看签名。
   `exact?` / `apply?` / `rw?` / `aesop` 鼓励用。
3. **公理审计。** 每条主定理证完跑 `#print axioms RBM.xxx`，只允许出现
   `propext` / `Classical.choice` / `Quot.sound`。出现 `sorryAx` 就是没做完。
   **不用 `native_decide`。**
4. **陈述逐字对应论文。** 不得不加假设（如 `3 ≤ L`）或换陈述形式，必须写进 `docs/paper-deltas.md`。
5. **小步提交。** 一次只动一条引理 / 一个文件；绿了就 `git commit`，不要攒一大坨再一起编译。
6. **不碰随机层**（Itô、Dyson Brownian motion、loop hierarchy、universality）。
   Mathlib 没有随机分析，那部分只写 `axiom` 接口，而且现在还不到时候。
7. **常数不求最优。** 统一写成 `∃ C > 0, ∃ c > 0, ∀ ...`；`≺` 用 `DetDom` 封装。
   §8 里所有 `∼` 都拆成显式的上界 + 下界两条，常数写死即可（现在 `(eq_elliptic)`
   的下界常数取的是 `1/9`，论文的论证给的是 `1/4`，无所谓）。

## 命名与风格

- namespace `RBM`（与 RBM1D 同名，两个项目不会同时 import，不冲突）
- 格点索引类型是 **`RBM.Z2 L := ZMod L × ZMod L`**，不是 `Fin 2 → ZMod L`。
  论文的 `|x|_L` 形式化为**周期 L¹ 距离** `RBM.zdist2`（论文明说 L¹ 与 L² 可互换）
- 变量约定：`L : ℕ`、`hL : 3 ≤ L`、谱参数 `ξ ζ : ℂ` 且 `‖ξ‖ < 1`、频率 `p : Z2 L`
- 文件头 copyright 块照抄现有文件
- 每落地一个声明，去 `blueprint/src/content.tex` 对应节点补 `\lean{}` + `\leanok`；
  节点名与论文的 label 一一对应（`lem:propTH`、`eq:elliptic`、`eq:Fourier_rep`）

## 分工：Claude Code 与 Cowork

两边都在用，边界按**迭代延迟**划，不按角色划。

| | Claude Code（本机） | Cowork / chat（云端） |
|---|---|---|
| 证明的试错循环 | **主场**。`lake env lean 单文件` 秒级返回 | 云端容器拉不到 Mathlib 的 olean cache（`lakecache.blob.core.windows.net` 被出口策略挡掉），**编不了** |
| 读论文 PDF / tex | `paper/` 下都有 | 同样都有 |
| 路线规划、阶段划分、开工单 | — | **主场** |
| 蓝图渲染 / 依赖图 | 需本机装 plasTeX + graphviz | 工具链现成 |
| git / CI / GitHub Pages | 都行 | 都行 |

**要点：Cowork 那边无法在本地编译。** 它写出来的 Lean 一律按「草稿」对待，
第一件事是拿到本机编译。这就是 T1 存在的原因。

**但 CI 可以当 Cowork 的编译器用。** GitHub 的 runner 拉得到 Mathlib 的 olean cache，
`lean_action_ci.yml` 会跑 `lake exe cache get` + `lake build`，日志里有全部报错。
所以 Cowork 侧的回路是「写 → push → 读 CI 日志 → 改」，一轮约 10 分钟。
本机 `lake env lean 单文件` 是秒级，所以**高频试错仍然归 Claude Code**；
CI 回路的用处是让 Cowork 写完的东西不至于原封不动地丢给对面去 debug。

### 任务队列

`docs/TASKS.md` 是两边共用的工单表。**开工前先在表里认领并提交**。
分工按**文件**切分，不按难度切分：同一时间两边不碰同一个文件，合并就永远是平凡的。

### 交接契约

`docs/STATUS.md` 是两边**唯一**的共享状态。任何一边：

- 开工前先读它
- 收工前更新它（新增了哪些声明、卡在哪、下一步是什么）
- 卡住时在里面写清楚「卡在 X，试过 Y 和 Z，失败原因是 W」，另一边才接得上

`docs/paper-deltas.md` 同理：偏离论文字面陈述的地方，谁发现谁记，不要只在对话里说。

### 共享同一个工作树

两边指向同一个文件夹、同一个 git 仓库、同一个工作树。所以：

1. **同时写同一个文件** —— 靠按文件切分避免。共享文档（`docs/*.md`、
   `blueprint/src/content.tex`、`CLAUDE.md`）改动要小、要立刻提交。
2. **git index.lock 争用** —— 撞到就等几秒重试。
3. **绝不用 `git add -A`** —— 只按文件名 `git add` 自己的那几个。
4. **`build.log` 是共用的** —— 读日志时按文件名过滤自己那部分。

### 常设授权

路由决策（某项工作该在哪边做）不必每次征求同意，按上表直接定。
需要征求同意的只有：改变项目范围、公开/删除内容、以及任何不可逆操作。

## 蓝图 / 站点

- 仓库：https://github.com/JYin80/Lean-RBM2d_arxiv-2503.07606
- 站点：https://jyin80.github.io/Lean-RBM2d_arxiv-2503.07606/ （Pages 要先在 Settings 里开，见 T12）
- **蓝图是这个项目唯一的进度真相。** 每落地一个声明，当场去
  `blueprint/src/content.tex` 对应节点补 `\lean{}` + `\leanok`，**和代码同一个 commit**。
- **只有 push 才会发布。** `docgen-action` 的上传与部署步骤条件是
  `github.event_name == 'push'`，手动 Run workflow 会「成功」但什么都不发布。
- `blueprint.yml` 只在 `RBM2D/**`、`blueprint/**`、`home_page/**`、`lakefile.toml`、
  `lean-toolchain` 改动时触发（doc-gen4 一次约半小时，不要为改 md 白跑）。
  `lean_action_ci.yml` 是每次 push 都跑的快速编译检查。

## 会话结束前的检查单

1. `./check.sh` → `build.log` 里 `errors: 0`、`exit=0`
2. `grep -rn "sorry" RBM2D/` → 空
3. 新落地的声明已在 `blueprint/src/content.tex` 里补了 `\lean{}` + `\leanok`，
   且 `leanblueprint checkdecls` 通过
4. 更新 `docs/STATUS.md`（新增的声明、下一步）
5. `git commit`
