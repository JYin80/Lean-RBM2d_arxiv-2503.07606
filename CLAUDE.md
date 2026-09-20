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

### Cowork 侧也有编译器了（2026-09-20）

在此之前 Cowork 只能「写 → 等 push → 读 CI」，一轮十几分钟，这是它产出慢的主因。
现在那个 Linux 沙箱 VM 里已经能跑 `lean`，一轮 **1–3 秒**：

```bash
# 一次性装好（VM 是 aarch64，$HOME 在 mnt/ 外面，用户看不到，会话结束即消失）
curl -sSL -C - -o ~/tc/lean.zip \
  https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-linux_aarch64.zip
python3 -c "import zipfile;zipfile.ZipFile('$HOME/tc/lean.zip').extractall('$HOME/tc')"
# 只把 ../RBM1D 已编译好的四类产物拷到本地盘（约 6 GB）：
#   *.olean  *.olean.server  *.olean.private  *.ir  *.ir.sig
# 直接用 mnt/ 下的会「Too many open files」——桥接挂载扛不住 import Mathlib 的并发句柄数
```

要点：

- **`ulimit -n 65536`**，否则 `import Mathlib` 直接挂。
- 不用 `lake`，直接 `lean -o <out>.olean <file>.lean`，`LEAN_PATH` 指到
  `~/pkgs/*` 加自己的 `~/build`。按依赖序编，全仓 14 个文件约 **23 秒**。
- 输出写 `~/build`，**不要写进用户的文件夹**。
- 判红看 `": error:"`，别看 stderr 非空 —— 警告也走 stderr。
- 磁盘只有 9.8 G，Mathlib 那六类产物占 5.6 G，删掉 toolchain 里的 `*.a`（链接用，
  类型检查不需要）能腾出 0.46 G。
- 脚本落在 `~/build.sh`（VM 本地，不进版本库）。**这套东西每个会话都要重装一次。**

CI 仍然是唯一的权威（那边是 `lake build`，会查到本机 `LEAN_PATH` 拼法掩盖不了的问题），
但本机这一轮把「名字猜错、tactic 不收敛」这类错误在 push 之前就清掉了。

## 构建回路

```bash
lake env lean RBM2D/Propagator/Xxx.lean   # 单文件，秒级 —— 默认用这个
./check.sh                                 # 全量，结果写进 build.log
./watch.sh                                 # 另开终端，改动即自动重编
```

**绝不在没有实际跑过编译的情况下说「写好了」。** 每次回报前必须有一次 exit=0。

## 硬性规则

**每个 agent 开工前先读这一节。** 这些不是习惯，是防返工的结构。

| 规则 | 为什么 |
|---|---|
| **不留 `sorry`**。证不出来就停下说「卡在 X」 | 共享工作树里一个 `sorry` 会让所有人的构建变红，而且**现在会直接编译失败**（见下一条） |
| **不许发明 Mathlib 引理名**。先 `grep -rn "foo" ~/Lean_proof/RBM1D/.lake/packages/mathlib/Mathlib/`，或 `#check @foo` 看签名 | 版本漂移是这类项目最大的时间黑洞。已核实的名字记进 `docs/mathlib-api.md`；**核实过不存在的也要记** |
| **公理审计写进了构建**：`RBM2D.lean` 末尾的 `#assert_rbm_axioms` 对整个 `RBM` 命名空间做硬检查 | 违规即**编译失败**。靠人记得跑 `#print axioms` 是靠不住的 —— 已用一个故意的 `sorry` 验证过它真的会挂 |
| **绝不写 `axiom`**。Mathlib 缺的东西写成 `structure` 字段或定理参数 | 这样下游立刻能编译、能并行；等基础设施到位**原地把字段换成定理，签名一个字不改**，依赖它的工单一张都不用返工。`axiom` 做不到，而且会污染公理审计。范例：`Propagator/Dyadic.lean` 的 `DyadicDecomp` |
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

### 分工：Cowork 只 commit，终端 agent 负责 push

**别指望 Cowork 侧 `git push`**，它跑在一个没有 keychain、没有 credential helper 的沙箱里：

```
$ git push --dry-run origin main
fatal: could not read Username for 'https://github.com': No such device or address
```

`git add` / `git commit` 只动本地 `.git`，不需要凭据，所以照常做。
**在 Mac 终端里常驻一个 Claude Code agent 负责 `git push`**（顺带跑 `lake build`）。
两边在同一个工作树上，它一 push 就把两边的 commit 一起推上去了。
**Claude Code 每次进这个仓库，第一件事和最后一件事都是 `git push`。**

提交身份统一为 `Jun Yin <321276894+JYin80@users.noreply.github.com>`（已在 `.git/config` 的
local 配置里），两边都不要用 `-c user.name=...` 覆盖。

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
5. **push 归终端的 Claude Code agent**，提交身份统一为 `Jun Yin` ——
   两条都在「硬性规则 → 分工」一节，不在这里重复。

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
