# 任务队列（RBM2D）

两边共用的工单。**认领前先改 `认领` 一栏并单独提交这一行**，避免重复劳动。

分工原则：**按文件切分，不按难度切分**。同一时间两边不碰同一个文件，合并就永远是平凡的。

| # | 任务 | 文件 | 认领 | 状态 |
|---|---|---|---|---|
| T1 | **把第一批草稿编译通过** | `RBM2D/**`（全部） | Cowork | **完成**（CI 绿，0 sorry） |
| T2 | `(eq_qcomp)`：`q(p) ≍ \|p\|²_*` | `Propagator/Momentum.lean`（新建） | 空闲 | **可开工** |
| T3 | 格点求和 `Σ_{p≠0} \|p\|_*^{-2} ≤ C L² log L` | `Propagator/LatticeSum.lean`（新建） | 空闲 | 待 T2 |
| T4 | 性质 5 在 `κL < 1` 区制 | `Propagator/Decay.lean`（新建） | 空闲 | 待 T3 |
| T5 | 性质 6 的 Case 2（`\|s\|_L > d/2`） | `Propagator/FiniteDiff.lean`（新建） | 空闲 | 待 T3 |
| T6 | `(deri_Thxi)`：`∂_ξ Θ = Θ S Θ` | `Propagator/Deriv.lean`（新建） | 空闲 | **可开工**，与 T2–T5 完全独立 |
| T7 | §2 模型层：`S = S^(B) ⊗ S_W`、`I^(2)_a`、`E_a` | `Defs/Model.lean`（新建） | 空闲 | **可开工**，独立 |
| T8 | 数值回归测试（`L = 3`，`ξ = 1/2`，在 ℚ 上） | `Test/Numeric.lean`（新建） | 空闲 | **可开工**，独立 |
| T9 | 无穷体积核 `(eq_Kinf)` + 围道平移 `(eq_shifted_lower)` | `Propagator/Contour.lean`（新建） | 空闲 | **第二批**，最硬 |
| T10 | 周期化 `K_{ξ,L} = Σ_n K_{ξ,∞}(·+nL)` | `Propagator/Periodize.lean`（新建） | 空闲 | 第二批，待 T9 |
| T11 | dyadic 分解 `(eq_dyadic)` + `(eq_dyadic_sum1/2)` | `Propagator/Dyadic.lean`（新建） | 空闲 | 第二批，待 T9 |
| T12 | 蓝图上线 | `blueprint/src/`、GitHub 设置 | Cowork | **大部分完成**，见下 |
| T13 | 扫掉剩下的 linter 警告 | `Defs/Dist.lean` 等 | 空闲 | **可开工，零风险** |

**T1 已完成（2026-09-19）**，`lake build` exit 0、0 sorry、10 个文件全绿。
剩下的建议顺序：**(T6 ∥ T7 ∥ T8) → T2 → T3 → (T4 ∥ T5) → 第二批。**

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

新建 `RBM2D/Propagator/Decay.lean`。论文 §8.2 的最后一段。依赖 T2、T3。

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

新建 `RBM2D/Propagator/FiniteDiff.lean`。论文 §8.3 的 "Case 2"。依赖 T3。
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
