# Blueprint

依赖图 / 蓝图，对照论文编号。绿色节点表示该节点标注的声明已在 Lean
中构建通过（`\leanok`）；若声明带有显式接口假设，绿色只表示条件命题已证。
协调任务审计并集成证明后才更新标记。

渲染需要 `leanblueprint`（Python）和 LaTeX：

```bash
pip install leanblueprint
cd ~/Lean_proof/RBM2D
leanblueprint checkdecls   # 校验每个 \lean{} 都能解析到真实声明
leanblueprint web          # 生成 docs/，含依赖图
leanblueprint pdf
```

本仓另有 `blueprint/render_artifact.py`，可从同一份 `content.tex` 生成
可缩放、拖动的单页交互依赖图；系统有 Graphviz `dot` 时使用其布局，
没有时自动使用内建 SVG 布局：

```bash
python3 blueprint/render_artifact.py . blueprint/web/artifact.html
```

上述 HTML 是本地生成物，不进版本库；每次更新 `content.tex` 或 Lean 证明后
重运行命令。生成器校验每个 `\lean{}` 引用，并同时绘制全文图与章节子图。
