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
单页依赖图；它需要系统安装 Graphviz 的 `dot`：

```bash
python3 blueprint/render_artifact.py . /tmp/rbm2d-blueprint.html
```

本地未安装渲染工具时，先检查节点数和 `\lean{}` 声明引用；最终由
推送后的 CI 完成全量构建与蓝图渲染。`content.tex` 本身始终可读。
