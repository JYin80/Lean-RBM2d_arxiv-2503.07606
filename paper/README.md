# 论文

- `2503.07606-aop-submission.pdf` —— 提交版 PDF（68 页），原始论文版本
- `tex/` —— 提交版的 LaTeX 源码，供检索与已裁定的局部勘误使用；勘误逐项记录在 `docs/paper-deltas.md`
- `tex/_stale/` —— 旧副本与模板，**不要读**（`3-4_properties-k-g-chains.tex` 是
  `3-4_properties-k-g.tex` 的过时重复，`8_theta_properties_OLD_backup.tex` 是
  Lemma `lem_propTH` 被 Fourier 证明替换之前的旧证明）

两者都在 `.gitignore` 里，不会推到公开仓库。

章节与文件的对应：

| 文件 | 内容 |
|---|---|
| `tex/1-2_intro-results-new.tex` | §1 引言、§2 模型与主定理（`MR:decol`、`lem_propTH`、`def_Theta`、`Def:G_loop`、`Def:oper_loop`、`Def_Ktza`） |
| `tex/3-4_properties-k-g.tex` | §3–4 K 与 G-loop 的性质 |
| `tex/5-6_loop-hierarchy-analysis.tex` | §5–6 loop hierarchy 与分析 |
| `tex/7_Evolution_kernel_estimates.tex` | §7 演化核估计 |
| `tex/8_theta_properties.tex` | **§8 `lem_propTH` 的证明** —— 当前 Phase 1 的全部目标 |

常用锚点（`grep -n` 进 `tex/`）：

- `\label{lem_propTH}` 性质 1–6 的陈述（`1-2` 第 801 行附近）
- `\label{eq_kappa_def}` κ 与 ℓ̂ 的定义
- `\label{eq_symbol}` Ŝ(p)；`\label{eq_Fourier_rep}` Fourier 表示
- `\label{eq_qdef}` q(p)；`\label{eq_qcomp}` q ≍ |p|²_*；`\label{eq_elliptic}` 椭圆性
- `\label{eq_Kinf}` 无穷体积核；`\label{eq_shifted_lower}` 平移后的下界
- `\label{eq_Kinf_bound}` (8.11)；`\label{eq_log_int}` 二维对数积分
- `\label{eq_dyadic}` dyadic 估计；`\label{eq_dyadic_sum1}`、`\label{eq_dyadic_sum2}` 两个求和
