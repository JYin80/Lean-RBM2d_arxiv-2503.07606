# CLAUDE.md — RBM2D

用 Lean 4 + Mathlib 形式化二维随机带状矩阵论文（arXiv:2503.07606，AOP 提交版）。
当前范围包括 §8 确定性内核与 §3–7 的随机层替代路线，详见 `docs/PLAN.md`。

姊妹项目：`../RBM1D`（d=1，arXiv:2501.01718）。**很多写法可以照抄那边**，但数学路线不同，见下。

## 唯一真相来源

- **论文**：`paper/2503.07606-aop-submission.pdf`（68 页），源码在 `paper/tex/`。
  **只依据这篇论文，不引用任何其他文献**（论文里引 `[YY_25]` 的地方，在 Lean 里当作假设或另开工单，不要去读 d=1 的论文来补证明）。
- **路线图**：`docs/PLAN.md`
- **当前进度**：`docs/STATUS.md` 顶部当前摘要；历史日志只供追溯
- **工单队列**：`docs/TASKS.md` 顶部当前表；协调任务统一认领和更新
- **与论文的偏差**：`docs/paper-deltas.md` —— 凡 Lean 陈述 ≠ 论文字面陈述，必须在这里记一条

## 与 d=1 的根本区别（这决定了整个项目的形状）

d=1 时最近邻三项递推有特征方程，闭式解 `(Θ_ξ)_{xy} = A(ξ)(ρ^d + ρ^{L−d})` 存在，
`RBM1D` 的衰减估计全部建立在它上面。**`Z_L^2` 上没有这种递推，闭式解不存在。**

所以 d=2 只有一条路：**§8 的 Fourier 路线**。
`Propagator/Symbol.lean`（Fourier 表示）和 `Propagator/Elliptic.lean`（椭圆性）
在 RBM1D 里是可选的结构性结果，在这里是**承重墙**。

§8 的四层结构，也就是 Phase 1 的四层：

1. **§8.1 Fourier 建立 + 椭圆性** `|1 − ξŜ(p)| ∼ κ² + |p|²_*` —— 已编译
2. **§8.2 衰减 `(prop:ThfadC)`** —— 连续核、围道平移与逆的唯一性周期化。**最硬的一块**
3. **§8.3 导数界 `(prop:BD1)(prop:BD2)`** —— 动量的 dyadic 分解
4. 其中 **κL < 1 区制**（§8.2 后半）和**导数界 Case 2** 只用椭圆性，不需要围道平移，
   难度与第 1 层相当，应当早做 —— 见 `docs/TASKS.md` 的 T3、T4

## 环境

Lean `4.34.0` / Mathlib `v4.34.0`，版本由 `lean-toolchain` 和
`lake-manifest.json` 锁定。每个独立工作树先准备依赖，再编译：

```bash
cd <本任务工作树>
lake exe cache get
lake build
```

若当前环境不能联网，先逐项核对两个仓库的 `lake-manifest.json` 中所有包的
commit，然后在 macOS 上用 `cp -cR ../RBM1D/.lake/packages .lake/packages` 建立
独立的 copy-on-write 副本。**不要建立指向 d=1 包树的可写符号链接。**

Mathlib 源码在 `.lake/packages/mathlib/Mathlib/` —— 找 API 就 grep 这里。

## 构建回路

```bash
lake build RBM2D.Propagator.Xxx            # 单模块，包含库的 leanOptions
./check.sh                                 # 全量，结果写进 build.log
```

**单文件 `lake env lean` 不施加库的全部 leanOptions，不能当作最终验收。**
交付前须有 `lake build <模块>` 的 exit=0；集成后须有全量构建的 exit=0。

## 硬性规则

**每个 agent 开工前先读这一节。** 这些不是习惯，是防返工的结构。

| 规则 | 为什么 |
|---|---|
| **不留 `sorry`**。证不出来就停下说「卡在 X」 | 共享工作树里一个 `sorry` 会让所有人的构建变红，而且**现在会直接编译失败**（见下一条） |
| **不许发明 Mathlib 引理名**。先 `grep -rn "foo" ~/Lean_proof/RBM1D/.lake/packages/mathlib/Mathlib/`，或 `#check @foo` 看签名 | 版本漂移是这类项目最大的时间黑洞。已核实的名字记进 `docs/mathlib-api.md`；**核实过不存在的也要记** |
| **公理审计写进了构建**：`RBM2D.lean` 末尾的 `#assert_rbm_axioms` 对整个 `RBM` 命名空间做硬检查 | 违规即**编译失败**。靠人记得跑 `#print axioms` 是靠不住的 —— 已用一个故意的 `sorry` 验证过它真的会挂 |
| **绝不写 `axiom`**。尚未证明的事实只能明确标成接口，并列入卸假设工单 | 接口字段必须有数学来源与可满足性检查；不能用可自由赋值的数据字段、改名后的假设或不可满足的条件让定理空真。范例：`Propagator/Dyadic.lean` 的 `DyadicDecomp` |
| **陈述逐字对应论文**；任何偏离记进 `docs/paper-deltas.md` | 要写明**论文第几处、改哪一段** —— 这样「论文要改多少」随时可以算出来 |
| **只按文件名 `git add`**，绝不 `git add -A` | `-A` 会把别人正在写的文件暂存进你的提交 |
| **小步提交**，一次一条引理；绿了就 commit | 攒一大坨再一起编译，错了无法二分 |
| **造轮子之前先查仓库** | `grep -rn "theorem.*sum_" RBM2D/` 比重证快得多 |
| **常数不求最优**，写死，不要 `∃ C` | `(eq_elliptic)` 下界现在取 `1/9`，论文给 `1/4`，无所谓 |
| **共享文件只做点插入，绝不整体重排** | 唯一的共享文件是根 import 列表 `RBM2D.lean` 和 `docs/*.md`。用 `sorted(set(lines))` 去重会把末尾的 `#assert_rbm_axioms` 搅进 import 块 |
| **不用 `native_decide`** | 它把编译器信任基扩大到整个 Lean 运行时 |

### 永不停工规则

**队列见底 = 全员停工，这是这个项目里唯一不可接受的状态。**
`docs/TASKS.md` 的队列**永远要比 agent 多**。如果你发现没有「空闲且可开工」的工单了，
**不要停下来等指令**，按这个顺序自己挑活，并在表里补一行说明你在做什么：

1. **储备工单** —— `docs/TASKS.md` 第三批里被挡住的那些，看依赖是不是已经解开了；
2. **维护** —— linter 警告、重复引理合并、把某个文件里通用的引理提到 `Defs/`；
3. **审计** —— 挑论文的一节逐处核对，产出下一批工单（这类工作产出过本项目最大的两笔减负）。

### 当前分工（2026-09-21 起）

协调任务维护 `docs/TASKS.md`、`docs/STATUS.md`、`docs/paper-deltas.md`、
`blueprint/src/content.tex` 与根 import，审计后集成、提交、推送并跟进 CI。
Lean 证明任务分别在独立工作树写分配给自己的 Lean 文件；不改共享文档、根 import，
不自行推送。约 30 分钟尚未完成时给协调任务一份中间报告。
数学陈述或范围变动交 Jun 裁定；文件归属、依赖顺序等路由由协调任务决定。

提交身份统一为 `Jun Yin <321276894+JYin80@users.noreply.github.com>`（已在 `.git/config` 的
local 配置里），两边都不要用 `-c user.name=...` 覆盖。

## 命名与风格

- namespace `RBM`（与 RBM1D 同名，两个项目不会同时 import，不冲突）
- 格点索引类型是 **`RBM.Z2 L := ZMod L × ZMod L`**，不是 `Fin 2 → ZMod L`。
  论文的 `|x|_L` 形式化为**周期 L¹ 距离** `RBM.zdist2`（论文明说 L¹ 与 L² 可互换）
- 变量约定：`L : ℕ`、`hL : 3 ≤ L`、谱参数 `ξ ζ : ℂ` 且 `‖ξ‖ < 1`、频率 `p : Z2 L`
- 文件头 copyright 块照抄现有文件
- 每落地一个声明，在报告里给出对应论文编号；协调任务在审计通过后补
  `blueprint/src/content.tex` 的 `\lean{}` + `\leanok`。

## 工单与交接

- `docs/TASKS.md` 是协调任务维护的队列。每张工单写明论文编号、已有声明、
  可写文件、验收探针、编译要求及报告要求。描述可能过时，开工先对照代码与最新状态。
- 同时最多三个证明任务；各任务在独立工作树，只编辑分配给自己的 Lean 文件。
  协调任务集成时检查重名、根 import、全量构建和蓝图。
- 新假设先查量词与实际使用范围，并给出非退化的可满足性见证。
  若论文字面陈述为假，停止强行证明，精确报告反例或所差因子。
- 完成报告列出已编译声明、模块构建退出码、仍存的具名假设及下游解除的缺口。
  只读探针须标明“已编译但未入库”。
- `docs/STATUS.md` 顶部是当前摘要，后面的旧日志只作历史资料；
  `docs/paper-deltas.md` 记录所有陈述差异，不能把推测写成已证事实。

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
