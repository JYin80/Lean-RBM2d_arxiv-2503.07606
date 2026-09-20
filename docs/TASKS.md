# 任务队列（RBM2D）

两边共用的工单。**认领前先改 `认领` 一栏并单独提交这一行**，避免重复劳动。

分工原则：**按文件切分，不按难度切分**。同一时间两边不碰同一个文件，合并就永远是平凡的。

| # | 任务 | 文件 | 认领 | 状态 |
|---|---|---|---|---|
| T1 | **把第一批草稿编译通过** | `RBM2D/**`（全部） | Cowork | **完成**（CI 绿，0 sorry） |
| T2 | `(eq_qcomp)`：`q(p) ≍ \|p\|²_*` | `Propagator/Momentum.lean`（新建） | Cowork | **完成**（CI #18 绿，0 sorry） |
| T3 | 格点求和 `Σ_{p≠0} \|p\|_*^{-2} ≤ C L² log L`（**现在只剩组装**） | `Propagator/LatticeSum.lean`（新建） | 空闲 | **可开工**（T2、T15、T16 全部完成，只剩把三条乘起来） |
| T4 | 性质 5 在 `κL < 1` 区制 | `Propagator/Decay.lean`（新建） | 空闲 | 待 T3 |
| T5 | 性质 6 的 Case 2（`\|s\|_L > d/2`） | `Propagator/FiniteDiff.lean`（新建） | 空闲 | 待 T3 |
| T6 | `(deri_Thxi)`：`∂_ξ Θ = Θ S Θ` | `Propagator/Deriv.lean`（新建） | 空闲 | **可开工**，与 T2–T5 完全独立 |
| T7 | §2 模型层：`S = S^(B) ⊗ S_W`、`I^(2)_a`、`E_a` | `Defs/Model.lean`（新建） | 空闲 | **可开工**，独立 |
| T8 | 数值回归测试（`L = 3`，`ξ = 1/2`，在 ℚ 上） | `Test/Numeric.lean`（新建） | 空闲 | **可开工**，独立 |
| T9 | 无穷体积核 `(eq_Kinf)` + 围道平移 `(eq_shifted_lower)` | `Propagator/Contour.lean`（新建） | 空闲 | **第二批**，最硬 |
| T10 | 周期化 `K_{ξ,L} = Σ_n K_{ξ,∞}(·+nL)` | `Propagator/Periodize.lean`（新建） | 空闲 | 第二批，待 T9 |
| T11 | dyadic 分解 `(eq_dyadic)` + `(eq_dyadic_sum1/2)` | `Propagator/Dyadic.lean`（新建） | 空闲 | 第二批，待 T9 |
| T12 | 蓝图上线 | `blueprint/src/`、GitHub 设置 | Cowork | **大部分完成**，见下 |
| T13 | 扫掉剩下的 linter 警告 | `Defs/Dist.lean` 等 | Cowork | **完成**（全仓 0 warning） |
| T14 | 零模分离：把 `(eq_Fourier_rep)` 的 `p = 0` 项拎出来 | `Propagator/ZeroMode.lean`（新建） | Cowork | **完成**（CI #25 绿，0 sorry） |
| T15 | `max`-壳层计数 `#{p : k(p) = k} ≤ 12k + 4` | `Propagator/Shells.lean`（新建） | Cowork | **完成**（本机编译通过，0 sorry，0 warning，`#print axioms` 干净） |
| T16 | 调和和 `Σ_{k≤L} 1/k ≤ 1 + log L` 与 `≺ 1` 的桥 | `Propagator/Harmonic.lean`（新建） | Cowork | **完成**（CI #22 绿，0 sorry，0 warning） |
| T17 | dyadic 几何级数 `(eq_dyadic_sum1)(eq_dyadic_sum2)` | `Propagator/GeomSum.lean`（新建） | Cowork | **完成**（本机编译通过，0 sorry，0 warning，`#print axioms` 干净） |

**T1 已完成（2026-09-19）**，`lake build` exit 0、0 sorry、10 个文件全绿。
剩下的建议顺序：**(T6 ∥ T7 ∥ T8 ∥ T13 ∥ T14 ∥ T15 ∥ T16) → T3 → (T4 ∥ T5) → 第二批。**
T2 已完成（Cowork，CI #18 绿）。

**队列现在有 6 条可立刻开工且文件两两不相交的工单**（T6、T7、T8、T13、T15、T17；
T14 已由 Cowork 认领并写完草稿），足够两个 Claude Code 实例各取一条连着跑好几轮而不会撞车。
**T15 是其中唯一在关键路径上的**：T2 与 T16 都已完成，T15 一落地 T3 就只剩组装，
T3 一通 T4 与 T5 就都能并行开工。T14 的草稿一旦 CI 绿，T4 与 T5 的前置就只剩 T3。

T6/T7/T8 放在 T2 前面不是因为它们更重要，而是因为它们**互不相干且都短**，
适合在 T1 刚打通、对本项目的 API 还不熟的时候练手；而 T2→T3→T4 是一条串行链。

---

## T13 — 扫掉剩下的 linter 警告（**零风险，适合当练手**）

`lake build` 现在是绿的，但还有一批风格警告。本机有编译器的话几分钟就能扫完：

| 位置 | 警告 | 建议 |
|---|---|---|
| `Defs/Dist.lean` 118–122（5 处） | `show` 只该用来标注中间目标 | 把 `show zdist L a + zdist L b ≤ 1` 换成 `simp only [zdist2]`（它会顺带做投影归约），或者 `unfold zdist2` |
| `Defs/Dist.lean` 80、125 | `if_neg` 已弃用，建议 `ite_eq_right` | 两者陈述不同，不是直接替换，**先确认再改**；`RBM1D` 那边同样写法 |
| `Defs/Dist.lean` 32、67；`Propagator/Basic.lean` 43；`Propagator/Elliptic.lean` 181、189、206、212 | section 变量 `[NeZero L]` 没用上 | 按 linter 的提示在定理前加 `omit [NeZero L] in` |

**都是警告不是错误**，不影响 `lake build` 的退出码；但这个项目的规矩是日志干净，所以值得清掉。
清完在 `docs/STATUS.md` 里记一句。

---

## T1 — 把第一批草稿编译通过（**已完成**）

第一批文件是 **Cowork 侧写的，一行都没有编译过**。Cowork 所在的云端容器拉不到
Mathlib 的 olean cache（出口策略挡掉了 `lakecache.blob.core.windows.net`），
所以那边永远只能写、不能编。**这条工单就是把草稿变成定理。**

### 步骤

```bash
cd ~/Lean_proof/RBM2D
lake exe cache get
lake build          # 或者 ./check.sh
```

然后逐个文件 `lake env lean RBM2D/Xxx.lean` 修到绿。建议顺序按依赖：

```
Defs/Block → Defs/Dist → Propagator/Basic → Propagator/Bounds
           → Propagator/Symbol → Propagator/Elliptic
Defs/Domination、Delocalization 独立（是 RBM1D 的逐字复制，风险最低）
```

### 已知的高风险点（按文件）

**`Defs/Block.lean`**
- `card_sbSupport` 与 `sum_over_sbSupport` 里四个 `Finset.card_insert_of_notMem` /
  `Finset.sum_insert` 的 `∉` 副目标，我用的是
  `simp [Prod.ext_iff, h01, h0m, h01.symm, h0m.symm, h1m]`。
  需要的事实只有三条：`(0:ZMod L) ≠ 1`、`(0:ZMod L) ≠ -1`、`(1:ZMod L) ≠ -1`（都已备好）。
  simp 集不对就手写 `Finset.mem_insert` 展开 + `push_neg`。
- `neg_mem_sbSupport` 里的 `Prod.neg_mk`，以及收尾的 `tauto`。
- 这两条是整个文件唯一需要「五点互异」的地方；**改对一次，后面都不再碰**。

**`Defs/Dist.lean`**
- `zdist_eq_zero_iff` 用了 `rwa [ZMod.natCast_val, ZMod.cast_id] at hz`。
  这是 Mathlib 里标准的 `ZMod` 往返写法，但签名要确认。
- `zdist2_le_one_of_mem_sbSupport` 的五个分支用 `show zdist L a + zdist L b ≤ 1` 把
  `zdist2` 按定义展开，靠 `show` 的 defeq。若 `zdist2` 不肯展开就加 `unfold zdist2`。
- 1 维的 `zdist_*` 全部是 `RBM1D/Defs/Dist.lean` 的逐字复制，**那边已经绿了**。

**`Propagator/Basic.lean`** —— 风险最低，是 `RBM1D/Propagator/Basic.lean` 的机械移植
（`ZMod L` → `Z2 L`，`3` → `5`，`card_sbSupport = 3` → `= 5`）。唯一新东西是
`Finset.sup_const Finset.univ_nonempty 1` 需要 `Nonempty (Z2 L)`，由 `NeZero L` 给出。

**`Propagator/Bounds.lean`** —— 同上，只换了索引类型。

**`Propagator/Symbol.lean`** —— 新写的，风险中等：
- `inv_mul_sum_chr`：`Fintype.sum_prod_type` 与 `Finset.sum_mul_sum` 的方向可能要调，
  接着的 `mul_mul_mul_comm` 是 `(a*b)*(c*d) = (a*c)*(b*d)`，方向要对。
- `SB_mulVec_apply`：`e0/e1/e2` 三条把 `x - (0,0) / (-1,0) / (0,-1)` 换成
  `x / x+(1,0) / x+(0,1)`，用的是 `show ((0:ZMod L),(0:ZMod L)) = (0 : Z2 L) from rfl`
  和 `Prod.neg_mk`。如果 `rfl` 不认，就用 `Prod.mk_zero_zero`。
- `fourierKernel_sub_SB_mulVec`：最后那个 `calc` + `ring`。结构是 RBM1D 同名引理的
  三项版扩成五项版，`key` 那条恒等式在 `rw [hDdef, Shat]` 之后应当纯 `ring` 可证。
  若 `set C := ...` / `set D := ...` 妨碍了 `ring`，直接删掉 `set` 写全。
- `Theta_eq_circulant_fourierKernel`：`circulant_mul`、`circulant_mul_comm`、
  `circulant_single_one ℂ (Z2 L)`、`circulant_inj` 的实例要求（`Z2 L` 是 `AddCommGroup`
  且 `DecidableEq`，都满足）。

**`Propagator/Elliptic.lean`** —— 新写的，风险主要在三个 Mathlib 名字：
```
Complex.abs_re_le_norm            旧名 Complex.abs_re_le_abs
Complex.abs_im_le_norm            旧名 Complex.abs_im_le_abs
Complex.norm_le_abs_re_add_abs_im 旧名 Complex.abs_le_abs_re_add_abs_im
```
它们被隔离在文件开头的 `section ComplexAux` 三条 `*_aux` 引理里，**只需要改那三行**。
实在找不到就从 `Complex.normSq` 出发用 `nlinarith` 自己证（`‖z‖² = re² + im²`）。
另外 `norm_one_sub_mul_real_ge` 的第二个分支里有两处 `nlinarith`，给的 hint 可能不够，
需要时把 `hsplit`、`haabs`、`hge1`、`hge2` 再显式喂一遍。
`Real.sq_sqrt`、`Real.cos_le_one`、`Real.neg_one_le_cos` 是稳的。

### 完成标准

`./check.sh` 里 `errors: 0`、`exit=0`；`grep -rn "sorry" RBM2D/` 为空；
对下面这几条跑 `#print axioms`，只出现 `propext / Classical.choice / Quot.sound`：

```
RBM.Theta_transpose  RBM.Theta_apply_add_right  RBM.Theta_commute  RBM.Theta_eq_tsum
RBM.sum_Theta_row    RBM.Theta_apply_fourier    RBM.norm_one_sub_mul_Shat_ge
RBM.sq_norm_eigenvector_le_im_green
```

**凡是你改了陈述（不只是证明）的地方，记进 `docs/paper-deltas.md`。**
凡是你发现 Cowork 写错了数学（不是写错了 Lean），**在 `docs/STATUS.md` 里说清楚**。

---

## T2 — `(eq_qcomp)`：`q(p) ≍ |p|²_*`

新建 `RBM2D/Propagator/Momentum.lean`。论文 `tex/8_theta_properties.tex`，
`(eq_qdef)` 与 `(eq_qcomp)`。**纯实分析，与矩阵无关。**

`Propagator/Elliptic.lean` 里已经有 `RBM.qsym`：
```
qsym L p = 2/5 * ((1 - cos(2π p₁.val / L)) + (1 - cos(2π p₂.val / L)))
```
现在要把它和论文的 `|p|²_* = dist(p₁, 2πZ)² + dist(p₂, 2πZ)²` 比较。

### 关键简化：在格点上 `dist` 就是 `zdist`

对 `p : ZMod L`，论文的 `dist(2π p.val / L, 2πZ)` 恰好等于 `2π · zdist L p / L`
（`zdist` 已在 `Defs/Dist.lean` 里）。所以**不要去形式化 `dist(·, 2πZ)`**，直接定义

```lean
noncomputable def pstar (p : ZMod L) : ℝ := 2 * Real.pi * (zdist L p) / L
noncomputable def pstar2 (p : Z2 L) : ℝ := (pstar L p.1) ^ 2 + (pstar L p.2) ^ 2
```

并证
```lean
theorem cos_eq_cos_zdist (p : ZMod L) :
    Real.cos (2 * Real.pi * p.val / L) = Real.cos (pstar L p)
```
理由：`zdist = min p.val (L - p.val)`；`p.val ≤ L - p.val` 时两者相同，
否则 `cos(2π(L - p.val)/L) = cos(2π - 2π p.val/L) = cos(2π p.val/L)`，
用 `Real.cos_sub` / `Real.cos_two_pi_sub`（名字先 grep）。

**这一步是整条工单的支点**，把周期距离的所有麻烦压缩成一条余弦恒等式。

### 然后是一条纯粹的一元不等式

对 `θ ∈ [0, π]`：
```
(2/π²) θ² ≤ 1 - cos θ ≤ θ²/2
```
- 上界：`1 - cos θ = 2 sin²(θ/2) ≤ 2 (θ/2)² = θ²/2`，用 `Real.sin_le`（`0 ≤ x → sin x ≤ x`）。
- 下界：Jordan 不等式 `(2/π) x ≤ sin x` 对 `x ∈ [0, π/2]`。Mathlib 里大概是
  `Real.mul_le_sin`，**先 grep 确认**。于是 `2 sin²(θ/2) ≥ 2 (2/π · θ/2)² = (2/π²) θ²`。
- `1 - cos θ = 2 sin²(θ/2)`：grep `Real.cos_sq_half` / `Real.sin_sq_half` /
  `Real.cos_eq_one_sub_two_mul_sin_sq` 之类。

注意 `pstar L p ∈ [0, π]`：因为 `zdist L p ≤ L/2`。这条要单独证（`zdist_le_half`）。

### 产出

```lean
theorem qsym_le_pstar2 (p : Z2 L) : qsym L p ≤ (1/5 : ℝ) * pstar2 L p
theorem pstar2_le_qsym (p : Z2 L) : (4 / (5 * Real.pi ^ 2)) * pstar2 L p ≤ qsym L p
```
常数不求最优，能用就行。再把 `Elliptic.lean` 的 `(eq_elliptic)` 改写成
论文原式 `|1 - ξŜ(p)| ∼ κ² + |p|²_*` 的形式，作为 `norm_one_sub_mul_Shat_ge_pstar`。

---

## T3 — 格点求和 `Σ_{p ≠ 0} |p|_*^{-2} ≤ C L² log L`

新建 `RBM2D/Propagator/LatticeSum.lean`。依赖 T2 的 `pstar2`。

> **2026-09-19 更新：这条已经被拆小了。** 分层记账现在是 **T15**（`Propagator/Shells.lean`），
> 调和和到 `≺` 的桥现在是 **T16**（`Propagator/Harmonic.lean`），两条都能立刻开工。
> 剩给 T3 的只有组装：T15 的 `sum_erase_zero_eq_sum_shells` 分层，逐层用
> `pstar2 ≥ (2π k/L)²`（由 T2 的 `pstar` 定义直接算），套 T15 的 `card_shell_le`，
> 最后接 T16 的 `harmonic_detDom_one`。**下面原文里关于分层和调和和的段落已经归 T15/T16，
> 不要在 T3 里重写。**

这是 §8.2（`κL < 1` 区制）和 §8.3（Case 2）**共用**的唯一非平凡引理，
在论文里是一句「`≤ C log L`」带过的。

### 证法（按 `max` 分层，不要按 Euclid 范数分层）

令 `k(p) := max(zdist L p.1, zdist L p.2)`。则

1. `pstar2 L p ≥ (2π k(p) / L)²`（两个分量里大的那个就够了）
2. `#{p : k(p) = k} ≤ 8k`（边长 `2k+1` 的方框减去边长 `2k-1` 的方框；
   `(2k+1)² - (2k-1)² = 8k`。在 `ZMod L` 上 `zdist = k` 的点至多 2 个，所以
   `#{p : k(p) = k} ≤ 2·2·(2k+1) ≤ 8k + 4`，取 `≤ 12k` 之类的松界即可）
3. 于是
   ```
   Σ_{p ≠ 0} 1/pstar2 ≤ Σ_{k=1}^{L} 12k · L²/(4π² k²) = (3L²/π²) Σ_{k=1}^{L} 1/k
   ```

### 产出

```lean
theorem sum_inv_pstar2_le (hL : 3 ≤ L) :
    ∑ p ∈ Finset.univ.erase (0 : Z2 L), (pstar2 L p)⁻¹
      ≤ (3 / Real.pi ^ 2) * (L : ℝ) ^ 2 * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹
```

再加一条把调和和接到 `≺` 上的桥：
```lean
theorem harmonic_detDom_one : (fun L => ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) ≺ (fun _ => 1)
```
（`Σ_{k≤L} 1/k ≤ 1 + log L ≤ C_ε L^ε`。Mathlib 里有调和和与 `log` 的比较，
grep `Finset.sum_range_one_div_le` / `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` 之类；
实在没有就用 `Real.log` 的单调性 + `Real.add_one_le_exp` 自己搭。
**注意 `DetDom` 的序列参数在本项目里是 `L` 不是 `N`**，见 `Defs/Domination.lean` 的文件头。）

分层求和在 Lean 里用 `Finset.sum_le_sum_of_subset` + `Finset.sum_fiberwise`（或
`Finset.sum_biUnion`）。**这条工单的成本主要在分层的 Finset 记账，不在不等式。**
如果卡住，先把结论减弱成 `≤ C L^3`（把 1/k 换成 1）也可以 —— 对 T4 的
`κ²L² < 1` 区制**不够**，但对 T5（Case 2 只要 `≺ 1`，而 `C log L ≺ 1`）够。
真要减弱就在 `docs/STATUS.md` 里写清楚减弱了什么。

---

## T4 — 性质 5 `(prop:ThfadC)` 在 `κL < 1` 区制

新建 `RBM2D/Propagator/Decay.lean`。论文 §8.2 的最后一段。依赖 T2、T3、**T14**。

> **2026-09-19 更新：下面的「步骤 1 零模分离」已经独立成 T14**
> （`Propagator/ZeroMode.lean`），因为 T5 的第一步是同一条引理。
> T4 直接用 T14 的 `Theta_apply_eq_zero_mode_add` 和 `norm_chr`，不要自己再摘一遍零模。

论文原文（照抄，不要改）：设 `κL < 1`，于是 `ℓ̂ = L`，
```
|K_{ξ,L}(x)| ≤ 1/(L²|1-ξ|) + (C/L²) Σ_{p ≠ 0} 1/|p|²_*
            ≤ 1/(κ²L²) + C log L ≺ 1/(κ²L²)
```
最后一步用 `κ²L² < 1`。又 `|x|_L ≤ CL = Cℓ̂`，所以 `exp(-c|x|_L/ℓ̂)` 有正的下界，
而 `|1-ξ| ℓ̂² = κ²L²`，于是这就是 `(prop:ThfadC)`。

### 在 Lean 里怎么拆

1. **零模分离**：从 `Theta_apply_fourier` 出发，把 `p = 0` 那一项单独拿出来。
   `Shat L 0 = 1`（五项都等于 1），所以那一项是 `(L²)⁻¹ · 1/(1-ξ)`。
   用 `Finset.sum_eq_add_sum_diff_singleton` 或 `Finset.add_sum_erase`。
2. **其余模**：`‖chr L p x‖ = 1`（`AddChar.norm_apply`），分母用
   `norm_one_sub_mul_Shat_ge_pstar`（T2 的产出），得
   `‖·‖ ≤ 9 / (κ² + |p|²_*) ≤ 9 / |p|²_*`，再套 T3。
3. **组装**：先证一条**不带 `≺` 的显式不等式**
   ```lean
   theorem norm_Theta_apply_le_of_kappa_mul_L_lt_one (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1)
       (hsmall : kappa ξ * L < 1) (a b : Z2 L) :
       ‖Theta L ξ a b‖ ≤ (kappa ξ ^ 2 * L ^ 2)⁻¹
         + C * ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹
   ```
   再单独一条把它翻译成论文的 `≺` 形式。**两步分开，不要一次到位**，
   否则 `≺` 的 filter 记账会和不等式纠缠在一起。
4. 指数因子：`κL < 1` 时 `ℓ̂ = L`，`|x|_L ≤ L`（`zdist2 ≤ 2·(L/2) = L`），
   所以 `exp(-c|x|_L/ℓ̂) ≥ exp(-c)`，是个常数。**这一步是纯粹的放缩，不要漏了它** ——
   论文的结论带指数因子，我们的上界不带，所以要乘回 `exp(c)`。

### 不要做

`κL ≥ 1` 的那一半（围道平移 + 周期化）是 T9、T10。**这条工单只做 `κL < 1`。**
文件末尾留一条注释说明另一半在哪条工单，**不要写 `sorry`**。

---

## T5 — 性质 6 的 Case 2（`|s|_L > d/2`）

新建 `RBM2D/Propagator/FiniteDiff.lean`。论文 §8.3 的 "Case 2"。依赖 T3、**T14**。

> **2026-09-19 更新：下面的「步骤 1 零模消掉」已经独立成 T14**
> （`Propagator/ZeroMode.lean`）。T5 直接用 T14 的 `Theta_apply_sub_eq_erase_sum`。
**与 T4 完全独立，可以并行。**

论文的论证只有三行：零模是常数，从两个差分里都消掉，于是由 `(eq_elliptic)`
```
|K(x) - K(x-s)| + |2K(x) - K(x-s) - K(x+s)| ≤ (C/L²) Σ_{p≠0} 1/(κ² + |p|²_*) ≤ C log L
```
所以两个差分都是 `O(log L) ≺ 1`。另一方面 `s ≠ 0` 时 `|s|_L ≥ 1` 且 `d < 2|s|_L`，故
```
|s|_L/(d+1) ≥ c,   |s|²_L/(d²+1) ≥ c
```
`s = 0` 平凡。

### 在 Lean 里怎么拆

1. `Theta_apply_fourier` 代入三个点，作差。**零模消掉**这一步在 Lean 里是
   `chr L 0 u = 1`（`chr` 在 `p = 0` 时恒为 `stdAddChar 0 = 1`），所以差分里
   `p = 0` 的贡献是 `1/(1-ξ) · (1 - 1) = 0`。先把这条单独写成引理。
2. 其余模：`‖chr p x - chr p (x-s)‖ ≤ 2`，分母用椭圆性，套 T3。
3. 组合数：`d < 2|s|_L` 且 `|s|_L ≥ 1` ⟹ `|s|_L/(d+1) ≥ 1/3`。
   （`d + 1 < 2|s|_L + 1 ≤ 3|s|_L`。）第二条同理。
   **这几步是 `Nat`/`ℝ` 的算术，`omega` + `positivity` 就够。**
4. 产出两条显式不等式（Case 2 版的 `(prop:BD1)`、`(prop:BD2)`），
   `≺` 的包装单独一条。

`d := zdist2 L (a - b)`，`|s|_L := zdist2 L s`，都已在 `Defs/Dist.lean` 里。

---

## T6 — `(deri_Thxi)`：`∂_ξ Θ^(B)_ξ = Θ^(B)_ξ S^(B) Θ^(B)_ξ`

新建 `RBM2D/Propagator/Deriv.lean`。论文 `1-2_intro-results-new.tex` 的 `(deri_Thxi)`。

**这条是 `RBM1D/Propagator/Deriv.lean` 的逐字移植**（那边 91 行、已绿）：
`ZMod L → Z2 L`，其余不动。三条结果：

| Lean | 内容 |
|---|---|
| `RBM.Theta_sub_Theta` | 预解式恒等式 `Θ_ζ - Θ_ξ = (ζ-ξ) Θ_ζ S Θ_ξ` |
| `RBM.continuousAt_Theta` | `ξ ↦ Θ_ξ` 连续 |
| `RBM.hasDerivAt_Theta_apply` | `(deri_Thxi)`，**逐元素形式** |

**逐元素而不是矩阵值**：RBM1D 那边记过原因（Matrix 上 Pi 拓扑与范数拓扑的实例菱形），
d=2 一样，照抄，并在 `docs/paper-deltas.md` 里记一条。

---

## T7 — §2 模型层：`S = S^(B) ⊗ S_W`、`I^(2)_a`、`E_a`

新建 `RBM2D/Defs/Model.lean`。论文 `1-2_intro-results-new.tex` 第 100–110 行附近：
> Note that the entries of `H` and `S` are indexed by `Z_{WL}^2`.

以及 `I^{(2)}_a := I_{a(1)} × I_{a(2)}`，`I_{a(i)} := [(a(i)-1)W + 1, a(i)W]`。

对照 `RBM1D/Defs/Model.lean`（234 行、已绿）来写，但**维度全部要升一维**：

* 主指标用**块/偏移** `(ZMod L × ZMod L) × (Fin W × Fin W)`，
  论文的 `Z_{WL}^2` 版本另写一份并证双射下逐元素相等（RBM1D 那边叫
  `Spaper_eq` / `Epaper_eq` / `split_bijective`，照抄结构）
* `S_W : Matrix (Fin W × Fin W) (Fin W × Fin W) ℂ`，全 `W⁻²`
* `Svar = SB ⊗ₖ S_W`（`Matrix.kroneckerMap`）
* `E_a`：块投影，`Σ_a E_a = W⁻² · I`（注意 d=2 是 `W⁻²` 不是 `W⁻¹`）
* 行和为 1、自伴

**先自己核对 `W⁻²` 这个因子**：RBM1D 是 `Σ_a E_a = W⁻¹ I`，d=2 块里有 `W²` 个格点，
所以应当是 `W⁻²`。对不上就去 PDF 里把 `E_a` 的定义抄准，**不要照我的猜测写**。

`RBM.SB` 已在 `Defs/Block.lean` 里，直接复用，不要重新定义。

---

## T8 — 数值回归测试

新建 `RBM2D/Test/Numeric.lean`。

`L = 3`、`ξ = 1/2` 时在 ℚ 上验证 `(1 - ξ·S^(B))·Θ = I`：
把 `S^(B)` 在 `Z_3^2`（9 × 9）上**独立于 `RBM.SB` 按论文重新写一遍**，
用精确高斯消元给出显式逆，`decide` / `norm_num` 双边验证，并验证行和 `= 2 = (1-ξ)⁻¹`。

价值在于它**独立于整条符号推导链**，能抓住定义层面的抄写错误 ——
特别是五点支撑集 `{(0,0), (±1,0), (0,±1)}` 有没有写漏写错，以及 `1/5` 的归一。
再加一条把独立定义和 `RBM.SB 3` 对上的引理（RBM1D 那边叫 `SB_five_apply`）。

`L = 5`（25 × 25）如果编译时间不可接受就别做，`L = 3` 已经够抓错。
**不要用 `native_decide`。**

---

## T12 — 让蓝图站点实时更新

蓝图骨架 `blueprint/src/content.tex` 已经写好了，节点与论文的 label 一一对应
（`def:SB`、`lem:propTH-1234`、`lem:elliptic`、`lem:qcomp`、`lem:decay-small`、
`lem:contour`、`lem:periodize`、`lem:dyadic` …），`\uses{}` 依赖边也连好了。
CI（`.github/workflows/blueprint.yml`）和首页（`home_page/`）是 `RBM1D` 那套的移植。

**现在缺的只有三件事：**

1. **`\leanok` 一个都还没加。** 这是故意的 —— T1 没跑通之前，说某个节点「已形式化」
   是假的。T1 绿了之后，逐个节点加 `\leanok`（定义/引理的语句块和证明块各一个），
   然后跑
   ```bash
   pip install leanblueprint
   leanblueprint checkdecls    # 校验每个 \lean{} 都解析到真实声明
   leanblueprint web
   ```
   `checkdecls` 是硬性门槛：**它不过就说明 `\lean{}` 里写了不存在的名字。**

2. **GitHub Pages 还没开。** 仓库 Settings → Pages → Source 选 **GitHub Actions**。
   开完之后第一次 push 到 `main` 就会发布到
   `https://jyin80.github.io/Lean-RBM2d_arxiv-2503.07606/`。

3. **注意 `docgen-action` 只在 `push` 事件上部署。** 手动 "Run workflow"
   会「成功」但什么都不发布 —— 这条 `RBM1D` 踩过，见那边的 `docs/STATUS.md`。
   `blueprint.yml` 的触发路径已经限定在 `RBM2D/**`、`blueprint/**`、`home_page/**`、
   `lakefile.toml`、`lean-toolchain`，所以只改 `docs/*.md` 不会白跑半小时的 doc-gen4。

**往后的规矩（写进 `CLAUDE.md` 的会话检查单里了）：**
每落地一个声明，当场去 `content.tex` 对应节点补 `\lean{}` + `\leanok`，
和代码一起提交。**不要攒着最后一起补** —— 蓝图的依赖图是这个项目唯一的进度真相，
攒着补就等于没有进度真相。依赖图配色：绿 = 已形式化，蓝 = 已陈述未证，
灰 = 只在蓝图里（随机层）。

---

---

## T14 — 零模分离（`Propagator/ZeroMode.lean`，**T4 与 T5 共用**）

论文 §8.2 和 §8.3 的第一步是同一件事：把 `(eq_Fourier_rep)` 里 `p = 0` 的那一项单独拎出来。
原来 T4 的步骤 1 和 T5 的步骤 1 写的是同一条引理 —— 两条工单各写一遍，要么重复劳动，
要么撞在同一个概念上。**提出来单独成一个文件，T4 和 T5 才真的文件互斥。**

依赖：只要 `Propagator/Symbol.lean`（已绿）。**不依赖 T2。可以立刻开工。**

### 要证的东西，按顺序

1. `Shat_zero : Shat L 0 = 1`。
   `Shat` 的定义是 `(1 + (χ(p₁) + χ(-p₁)) + (χ(p₂) + χ(-p₂)))/5`，`p = 0` 时五项都是 1。
   用 `AddChar.map_zero_eq_one`（**已在 pinned Mathlib 里核对过，且是 `@[simp]`**，
   在 `Mathlib/Algebra/Group/AddChar.lean:111`）。
   坑：`(0 : Z2 L).1` 到 `(0 : ZMod L)` 是 `rfl`，但 `simp` 未必自己走这一步，
   需要 `Prod.fst_zero` / `Prod.snd_zero`，以及 `neg_zero`。

2. `chr_zero_left : chr L 0 u = 1`。同上，`chr L p u = stdAddChar (p.1 * u.1 + p.2 * u.2)`，
   `p = 0` 时括号里 `zero_mul` 两次再 `add_zero` 就是 `0`。

3. `one_sub_mul_Shat_zero : 1 - ξ * Shat L 0 = 1 - ξ`，由第 1 条 `rw` + `mul_one`。

4. **零模分离**本体：
```lean
theorem Theta_apply_eq_zero_mode_add (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Z2 L) :
    Theta L ξ a b
      = ((L : ℂ) ^ 2)⁻¹ * (1 - ξ)⁻¹
        + ((L : ℂ) ^ 2)⁻¹ * ∑ p ∈ Finset.univ.erase (0 : Z2 L),
            chr L p (a - b) / (1 - ξ * Shat L p)
```
从 `Theta_apply_fourier` 出发，把 `p = 0` 摘出来。`Finset.add_sum_erase` 与
`Finset.sum_erase_add` **两个都存在、方向相反**（已核对），挑对的那个；
`(0 : Z2 L) ∈ Finset.univ` 由 `Finset.mem_univ` 给。摘出来的那一项用第 2、3 条化成
`1 / (1 - ξ) = (1 - ξ)⁻¹`（`one_div`）。最后 `mul_add` 把 `(L²)⁻¹` 分配进去。

5. **差分版**（T5 要的），零模在差分里自己消失：
```lean
theorem Theta_apply_sub_eq_erase_sum (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (u v : Z2 L) :
    Theta L ξ u 0 - Theta L ξ v 0
      = ((L : ℂ) ^ 2)⁻¹ * ∑ p ∈ Finset.univ.erase (0 : Z2 L),
          (chr L p u - chr L p v) / (1 - ξ * Shat L p)
```
两边用第 4 条展开，常数项相减为 0；求和里用 `sub_div` 合并（**方向别搞反**）和
`Finset.sum_sub_distrib`。陈述里固定 `b = 0` 是因为平移不变性
`Theta_apply_add_right` 已把一般情形化归到这里；`u - 0 = u` 用 `sub_zero`。

6. 范数侧的配套（T4、T5 都立刻要用，放这里省得两边各写一遍）：
```lean
theorem norm_chr (p u : Z2 L) : ‖chr L p u‖ = 1
```
`ZMod.stdAddChar : AddChar (ZMod N) ℂ` 定义为 `Circle.coeHom.compAddChar toCircle`
（`Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean:83`），所以值落在单位圆上；
先 `rw [chr, ZMod.stdAddChar_apply]`，再找 `Circle` 的陪域范数引理
（**`Circle.norm_coe` / `Circle.abs_coe` 名字先 grep 确认**）。
这条万一卡住就**先跳过**，在 `docs/STATUS.md` 里写一句「norm_chr 未落地」，
T4/T5 可以临时退到 `‖chr‖ ≤ 1` 的粗界（由 `Shat` 那边已有的手法）继续。
**不要写 `sorry`。**

### 完成标准
`lake env lean RBM2D/Propagator/ZeroMode.lean` exit 0、0 sorry；
第 4、5 条跑 `#print axioms` 只出现 `propext / Classical.choice / Quot.sound`；
蓝图节点 `lem:zero-mode` 补 `\lean{}` + `\leanok`。

---

## T15 — `max`-壳层计数（`Propagator/Shells.lean`）

T3 的成本原本几乎全在 Finset 记账上，和不等式无关。把记账单独拿出来做掉，
T3 就只剩「把三条现成引理乘起来」。

依赖：只要 `Defs/Dist.lean`（已绿）。**不依赖 T2，全程不碰实数**，所以能和 T2 并行。

### 要证的东西，按顺序

1. 壳层指标
```lean
def shellIndex (p : Z2 L) : ℕ := max (zdist L p.1) (zdist L p.2)
```

2. 一维层至多两个点：
```lean
theorem card_filter_zdist_eq_le (k : ℕ) :
    (Finset.univ.filter (fun u : ZMod L => zdist L u = k)).card ≤ 2
```
`zdist L u = min u.val (L - u.val) = k` 蕴含 `u.val = k` 或 `u.val = L - k`，
所以 filter 含于至多两元的 `{(k : ZMod L), ((L - k : ℕ) : ZMod L)}`；
用 `Finset.card_le_card` + `Finset.card_insert_le` + `Finset.card_singleton`。
**坑：`k ≥ L` 时 filter 是空的**（`zdist < L`），要先单独讨论，
否则 `ZMod.val_cast_of_lt` 的边界条件不成立。

3. 二维壳层：
```lean
theorem card_shell_le (k : ℕ) :
    (Finset.univ.filter (fun p : Z2 L => shellIndex L p = k)).card ≤ 12 * k + 4
```
`shellIndex p = k` 迫使某个坐标的 `zdist` 恰为 `k`、另一个 `≤ k`。把壳层写成
「第一坐标 `= k`」与「第二坐标 `= k`」两块的并（`Finset.card_union_le`，已核对存在），
每块是乘积集，用 `Finset.card_product` / `Finset.filter_product`；
每块 `≤ 2 * (2k + 1)`，合计 `≤ 8k + 4 ≤ 12k + 4`。
**常数松一点无所谓**，下游只要一个 `C·k`；写成 `12k + 4` 是为了 `k ≥ 1` 时能一步放成 `16k`。

4. 零壳层只有原点：`shellIndex L p = 0 ↔ p = 0`，由 `zdist_eq_zero_iff` 用两次
   （加 `Nat.max_eq_zero_iff`，名字先确认）。

5. 壳层指标的上界：`shellIndex L p ≤ L`。
   由 `zdist L u = min u.val (L - u.val) ≤ u.val < L`，一行 `omega`。
   **注意：`Propagator/Momentum.lean` 里有一条同类的 `two_mul_zdist_le`，那是 T2 的文件，
   不要 import 它**（会把两条工单绑在一起）；这里重证一行即可。

6. 分层求和的接口（T3 直接消费的那条）：
```lean
theorem sum_erase_zero_eq_sum_shells (f : Z2 L → ℝ) :
    ∑ p ∈ Finset.univ.erase (0 : Z2 L), f p
      = ∑ k ∈ Finset.Icc 1 L,
          ∑ p ∈ Finset.univ.filter (fun p => shellIndex L p = k), f p
```
走 `Finset.sum_fiberwise_of_maps_to`（**已核对存在**；注意它和 `Finset.sum_fiberwise`
签名不同，别拿错）。`maps_to` 的条件是「`p ≠ 0` ⟹ `shellIndex L p ∈ Finset.Icc 1 L`」，
由第 4、5 条给。

### 陷阱
- `Finset.filter` 要 `DecidablePred`：`zdist L u = k` 是 ℕ 上的相等，没问题；
  `Z2 L` 上还要 `DecidableEq (Z2 L)`，由 `Prod` 的实例给。撞到实例问题就在文件头
  写 `open Classical in`，但**先试不加**，加了会让 `decide` 系的东西变慢。
- 全程在 ℕ 和 `Finset` 里，一个实数都不出现。这就是它能和 T2 并行的原因。

### 完成标准
单文件编译 exit 0、0 sorry；第 3、6 条 `#print axioms` 干净；
蓝图节点 `lem:shells` 补 `\lean{}` + `\leanok`。

---

## T16 — 调和和与 `≺` 的桥（`Propagator/Harmonic.lean`）

T3 的产出里有一条 `Σ_{k ≤ L} 1/k ≺ 1`。它和格点毫无关系，是纯粹的
「Mathlib 的调和和 + `DetDom` 的定义」，**可以完全独立地先做掉。**

依赖：只要 `Defs/Domination.lean`（已绿）。**不依赖 T2、T3、T15。可以立刻开工。**

### Mathlib 已经有的（已在 pinned v4.34.0 源码里逐条核对）

`Mathlib/NumberTheory/Harmonic/Defs.lean`：
```
def harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹
```
`Mathlib/NumberTheory/Harmonic/Bounds.lean`：
```
lemma   harmonic_eq_sum_Icc {n : ℕ} : harmonic n = ∑ i ∈ Finset.Icc 1 n, (↑i)⁻¹   -- 在 ℚ 里
theorem harmonic_le_one_add_log (n : ℕ)  : (harmonic n : ℝ) ≤ 1 + Real.log n
theorem log_add_one_le_harmonic (n : ℕ)  : Real.log ↑(n + 1) ≤ harmonic n
```
所以 `import Mathlib.NumberTheory.Harmonic.Bounds` 就够，**不要自己造调和和**。

### 要证的东西，按顺序

1. 把 ℚ 版搬到 ℝ：
```lean
theorem sum_inv_Icc_le_one_add_log (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ ≤ 1 + Real.log n
```
由 `harmonic_eq_sum_Icc` + `harmonic_le_one_add_log`，中间推 cast 用
`Rat.cast_sum` / `Rat.cast_inv` / `Rat.cast_natCast`
（`harmonic_le_one_add_log` 自己的证明里就是这三个，照抄那一行 `simp_rw`）。

2. `log` 被任意小的幂压住 —— 这就是 `≺` 的全部内容：
```lean
theorem log_le_rpow_div {τ : ℝ} (hτ : 0 < τ) {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x ^ τ / τ
```
**不要去找现成的，三行自己证**：`Real.log_le_sub_one_of_pos`
（`Log/Basic.lean:307`，已核对）用在 `x ^ τ` 上给 `log (x^τ) ≤ x^τ - 1`；
`Real.log_rpow hx τ : log (x^τ) = τ * log x`（`Pow/Real.lean:494`，已核对）；
于是 `τ * log x ≤ x^τ - 1 ≤ x^τ`，两边除以 `τ > 0`。

3. 桥：
```lean
theorem one_add_log_detDom_one : (fun L : ℕ => 1 + Real.log L) ≺ (fun _ => (1 : ℝ))
```
按 `detDom_iff` 展开：给定 `τ > 0`，要找 `N₀` 使 `L ≥ N₀` 时 `1 + log L ≤ L^τ`。
由第 2 条 `log L ≤ L^{τ/2} / (τ/2)`，再用 `Defs/Domination.lean` 里现成的
`eventually_le_rpow`（`∀ᶠ N, C ≤ N^τ`）把常数 `1 + 2/τ` 吃掉，
用 `rpow_half_mul_rpow_half`（同一个文件，`N^{τ/2} · N^{τ/2} = N^τ`）拼起来。
**先读 `Defs/Domination.lean` 里 `trans` 的证明** —— 它就是这个套路的模板。

4. 组合出 T3 真正要的那条：
```lean
theorem harmonic_detDom_one :
    (fun L : ℕ => ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹) ≺ (fun _ => (1 : ℝ))
```
由第 1 条 + 第 3 条接起来。**订正（2026-09-19）：本工单原先写「用 `DetDom.mono_left`」，
`Defs/Domination.lean` 里没有这条** —— `mono_left` 只在 `UnifDetDom` 命名空间里，
`DetDom` 那边只转出了 `trans / add / mul / const_mul_*/ add_left / refl`。
改走 `rw [detDom_iff]` 展开成 `∀ᶠ` 再 `filter_upwards`，不依赖 `mono_left`。

### 陷阱
- `Real.log 0 = 0`、`Real.log 1 = 0`，`n = 0, 1` 不用特判，但放缩里要显式喂
  `Real.log_natCast_nonneg`（`Log/Basic.lean:225`，已核对）。
- **`DetDom` 的序列参数在本项目里是 `L` 不是 `N`**，见 `Defs/Domination.lean` 文件头。
- **不要用除法形式**。第 2 条若写成 `log x ≤ x^τ / τ`，收尾就需要
  `le_div_iff₀` / `div_le_div_of_nonneg_right` 这一族 —— 我在 pinned 源码里
  grep `le_div_iff₀` **没找到**，这族名字跨版本最不稳。写成乘法形式
  `τ * log x ≤ x^τ`，全文件一个除法引理都不需要。
- `rpow` 与 `pow` 不要混：`(L : ℝ) ^ (τ : ℝ)` 是 `Real.rpow`，`(L : ℝ) ^ (2 : ℕ)` 是
  `Monoid.npow`，桥是 `Real.rpow_natCast`（`Pow/Real.lean:62`，已核对）。
  `DetDom` 的定义里用的是 `rpow`。

### 完成标准
单文件编译 exit 0、0 sorry；第 4 条 `#print axioms` 干净；
蓝图节点 `lem:harmonic` 补 `\lean{}` + `\leanok`。

---

## T17 — dyadic 几何级数 `(eq_dyadic_sum1)` `(eq_dyadic_sum2)`（`Propagator/GeomSum.lean`）

T11 是全项目最硬的一块，但它其实是两件事拼起来的：
`(eq_dyadic)` 那条逐环估计（难，要离散分部求和），和把各环加起来的**两条几何级数**（不难，纯算术）。
`TASKS.md` 原文自己就写了「这两条是纯算术，可以先于 `(eq_dyadic)` 单独做掉」——
这条工单就是把它兑现，放进独立文件，这样 **T11 即使卡死或降级成引用接口，这两条也已经落地**。

依赖：只要 `Propagator/Elliptic.lean`（已绿，提供 `kappa`、`ellhat`、`kappa_mul_ellhat_le_one`）。
**不依赖 T9、T11、T2、T3。可以立刻开工。全程实数，不碰格点、不碰 Fourier。**

论文出处：`paper/tex/8_theta_properties.tex` 第 177–178 行。

### 怎么把「dyadic 求和」写成 Lean

论文的 `r` 跑遍 `L^{-1} ≲ r ≲ 1` 的二进值。在 Lean 里就取

```lean
noncomputable def dyad (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℤ))
```

求和范围是 `j ∈ Finset.range (J + 1)`，`J` 是参数（下游取 `J ≈ log₂ L`，
但**这条工单对 `J` 一致成立，不需要知道 `J` 和 `L` 的关系**）。
`dyad j ∈ (0, 1]`、`dyad` 单调减、`∑_{j<n} dyad j ^ k ≤ 2^k/(2^k − 1)`
这三条是文件的地基，先写。

### 固定 `M = 3`

论文说 `M` 可任意大。下面的拆分只用到 `M = 3`（见第 3 步），所以**在 Lean 里把 `M` 写死为 3**，
不引入额外参数。这是一处陈述与论文字面的偏差，落地时**记进 `docs/paper-deltas.md`**：
论文的 `∀ M` 我们只取一个够用的 `M`，下游 `(eq_fd1)(eq_fd2)` 用的也只是某一个 `M`。

### 要证的东西，按顺序

1. **地基**：`dyad_pos`、`dyad_le_one`、`dyad_antitone`，以及
```lean
theorem sum_dyad_pow_le (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    ∑ j ∈ Finset.range n, (dyad j) ^ k ≤ 2
```
（`∑_{j≥0} 2^{-jk} = 1/(1−2^{-k}) ≤ 2`。走 `Finset.geom_sum_le` 一族，
**名字先 grep**：`geom_sum_eq`、`Finset.geom_sum_le` 在 `Mathlib/Algebra/GeomSum.lean`。
若形状难调，退而证 `≤ 2` 的归纳版：`∑_{j<n+1} = 1 + (1/2^k)∑_{j<n}`。）

2. **第一次劈开：`r ≤ κ` 与 `r > κ`。** 把 `Finset.range (J+1)` 按
`decide (dyad j ≤ kappa ξ)` 分成两块（`Finset.sum_filter_add_sum_filter_not`，已核对存在）。
- `r ≤ κ` 那块：`κ² + r² ≥ κ²`，于是 `r³/(κ²+r²) ≤ r³/κ² ≤ r·(r/κ)² ≤ r ≤ κ`，
  求和用第 1 步得 `≤ 2κ`。再由 **`1/ℓ̂ = max(κ, 1/L) ≥ κ`** 换成 `≤ 2/ℓ̂`。
  （`ellhat = min(κ⁻¹, L)`，所以 `ellhat ≤ κ⁻¹`，即 `κ ≤ 1/ℓ̂`。
  `Elliptic.lean` 的 `kappa_mul_ellhat_le_one` 就是这条，直接用，别重证。）
- `r > κ` 那块：`κ² + r² ≥ r²`，于是被 `r·(1+rd)^{-3}` 控制。进第 3 步。

3. **第二次劈开：`r ≤ 1/(d+1)` 与 `r > 1/(d+1)`。**
- `r ≤ 1/(d+1)`：`(1+rd)^{-3} ≤ 1`，剩 `∑ r ≤ 2·max r ≤ 2/(d+1)`。
- `r > 1/(d+1)`：**关键一步**是 `1 + r·d ≥ r·(d+1)`，它成立**当且仅当 `r ≤ 1`**
  （`1 + rd − r(d+1) = 1 − r ≥ 0`），而 `dyad j ≤ 1` 正是第 1 步。
  于是 `(1+rd)^{-3} ≤ r^{-3}(d+1)^{-3}`，被求和项 `≤ r^{-2}(d+1)^{-3}`。
  这一块里 `r^{-1} < d+1`，`∑ r^{-2}` 在二进值上是递增几何级数，被最大项 `≤ (d+1)²` 的两倍控制，
  合计 `≤ 2(d+1)²·(d+1)^{-3} = 2/(d+1)`。
- **注意这里 `r^{-1} ≤ d+1` 这个上界是从 filter 条件 `dyad j > 1/(d+1)` 直接来的**，
  不需要知道 `J`。递增几何级数的求和界写成
  `∑_{j ∈ s} (dyad j)^{-2} ≤ 2 · (最大项)`，最大项由 filter 条件控制。

4. **产出**（`d : ℕ`，`ξ : ℂ`，`‖ξ‖ < 1`，`J : ℕ`）：
```lean
theorem dyadic_sum_three_le (hξ : ‖ξ‖ < 1) (d J : ℕ) :
    ∑ j ∈ Finset.range (J + 1),
        (dyad j) ^ 3 / (kappa ξ ^ 2 + (dyad j) ^ 2) * (1 + dyad j * d) ^ (-3 : ℤ)
      ≤ 8 * ((d : ℝ) + 1)⁻¹ + 8 * (ellhat ξ L)⁻¹

theorem dyadic_sum_four_le (hξ : ‖ξ‖ < 1) (d J : ℕ) :
    ∑ j ∈ Finset.range (J + 1),
        (dyad j) ^ 4 / (kappa ξ ^ 2 + (dyad j) ^ 2) * (1 + dyad j * d) ^ (-3 : ℤ)
      ≤ 8 * (((d : ℝ) ^ 2 + 1))⁻¹ + 8 * (ellhat ξ L) ^ (-2 : ℤ)
```
第二条的两次劈开与第一条逐字平行，只是幂次各加一：
`r ≤ κ` 给 `∑ r⁴/κ² ≤ 2κ² ≤ 2/ℓ̂²`；`r ≤ 1/(d+1)` 给 `∑ r² ≤ 2/(d+1)²`；
`r > 1/(d+1)` 给 `∑ r^{-1}(d+1)^{-3} ≤ 2(d+1)·(d+1)^{-3} = 2/(d+1)²`。
**先把第一条做完再抄第二条**，不要并行写两条。

### 陷阱
- **常数一律写死**，不要 `∃ C`。上面 `8` 是随手放松的，能过就行。
- `(1 + r*d) ^ (-3 : ℤ)` 是 `zpow`；底数 `1 + r*d > 0`（`positivity`），
  所以 `zpow_neg`、`one_div`、`inv_le_inv₀` 这一族可用。
  **`zpow` 与 `rpow` 不要混**，本文件全程 `zpow` 和 `Monoid.npow`，一个 `rpow` 都不要出现。
- `d : ℕ` 而不是 `ℝ`，因为下游的 `d = zdist2 L (a-b)` 是 ℕ。`(d : ℝ) + 1 > 0` 用 `positivity`。
- `kappa ξ > 0` 由 `Elliptic.lean` 的 `kappa_pos` 给（已绿），**需要 `ξ ≠ 1`**，
  而 `‖ξ‖ < 1` 蕴含它 —— 照 `Elliptic.lean` 里现成的用法抄，不要自己推。
- 这条工单**不碰 `(eq_dyadic)` 本身**。文件末尾留一条注释指向 T11，**不要写 `sorry`**。

### 完成标准
单文件编译 exit 0、0 sorry；第 4 步两条跑 `#print axioms` 干净；
`docs/paper-deltas.md` 里记一条「`M` 固定为 3」；
蓝图新增节点 `lem:dyadic-sums`（`\uses{lem:kappa-basic}`），补 `\lean{}` + `\leanok`。


# 第二批（围道那条线，暂不开工）

下面三条是 §8.2 的 `κL ≥ 1` 区制和 §8.3 的 Case 1，是整个项目最硬的部分。
**等 T1–T8 落地、对本项目的 API 熟了之后再动。** 先记下要点：

## T9 — 无穷体积核 `(eq_Kinf)` + 围道平移 `(eq_shifted_lower)`

`K_{ξ,∞}(x) = (2π)^{-2} ∫_{[-π,π]²} e^{ip·x}/(1-ξŜ(p)) dp`。

要证的核心是：对 `|η| ≤ c₀κ`，`|D_ξ(p + iη)| ≥ c(κ² + |p|²_*)`。
论文的推导是 `|q(p+iη) - q(p)| ≤ C(|η||p|_* + |η|²)`（由
`cos(u+iv) = cos u cosh v - i sin u sinh v` 与 `|sin u| ≤ dist(u, 2πZ)`），
再用 `κ|p|_* ≤ (κ² + |p|²_*)/2` 把扰动吸收进 `(eq_elliptic)` 的下界。

Mathlib 侧要先确认的零件（**先 grep，不要假设**）：
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`（矩形围道）、
`intervalIntegral` 的换元与周期性。

## T10 — 周期化 `K_{ξ,L}(x) = Σ_{n ∈ Z²} K_{ξ,∞}(x + nL)`

论文说「by Poisson summation, **or simply by comparing Fourier coefficients**」。
**走后者**：在 Lean 里「两个函数的 Fourier 系数相同」比 Poisson 求和定理的解析假设便宜得多。
具体就是：右边这个 `Z_L²` 上的函数，其在 `T_L²` 上的 Fourier 系数正好是
`1/(1-ξŜ(p))`，而左边按定义也是，再用 `Symbol.lean` 里已有的特征标正交性收口。

## T11 — dyadic 分解 `(eq_dyadic)` 与两个求和

`(eq_dyadic)`：`|∇^m K_r(x)| ≤ C_M r^{m+2}/(κ²+r²) (1 + r|x|_L)^{-M}`，`m = 0,1,2`。
机制论文写得很清楚：每次分部求和给一个 `(1+r|x|_L)^{-1}`，每次对乘子或截断求导
付一个 `r^{-1}`，环里有 `O(L²r²)` 个动量，乘子是 `O((κ²+r²)^{-1})`，
`x` 的每个导数给 `O(r)`。

`(eq_dyadic_sum1)`、`(eq_dyadic_sum2)` 是在 `r ∼ κ` 和 `r ∼ (d+1)^{-1}` 两处劈开的
几何级数求和，**这两条是纯算术，可以先于 `(eq_dyadic)` 单独做掉**，
作为独立引理放进 `Propagator/Dyadic.lean` 的开头。

---

## 给 Claude Code 的一句话

> 读 `docs/TASKS.md`，先做 **T1**：`lake exe cache get` → `lake build`，
> 把 Cowork 写的第一批草稿编译通过。开工前先在上面表格里把 `认领` 改成
> Claude Code 并**单独提交这一行的改动**。
>
> T1 里凡是你改了**陈述**（不只是证明）的地方，记进 `docs/paper-deltas.md`；
> 凡是发现数学写错了（不是 Lean 写错了），在 `docs/STATUS.md` 里说清楚。
>
> T1 绿了之后按 T6 → T7 → T8 → T2 → T3 → T4 ∥ T5 往下走。
> 规则照 `CLAUDE.md`：不留 sorry、不发明 Mathlib 引理名（先 grep 或 `#check`）、
> 每条主定理跑 `#print axioms`、`decide` 不用 `native_decide`、
> 只 `git add` 自己的文件名。
