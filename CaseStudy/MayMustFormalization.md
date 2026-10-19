# Revised Fig. 6：May/Must 的形式化

依据用户提供的 revised `main.pdf`，PDF 第 22–23 页 Fig. 6 和 §6。
两个开放程序的完整 `has_context_type` 推导及其 `concrete_Fundamental`
推论均已通过 Rocq 验证。`g` 是满足论文规约的任意自由函数变量。

采用论文记号：$\{\nu:b\mid\phi\}$ 表示 Over，$[\nu:b\mid\phi]$
表示 Under，$\to$ 表示 entangled arrow，$-\!*$ 表示 independent arrow。
$\oplus$ 的两部分均须非空。

## 例 (a)：May-analysis helps must-analysis

当前采用用户要求的变体：将论文的 $y>10$ 改为 $y\ge10$，类型保持不变。
实现使用整数上等价的 `op_int_gt 9`；`may_help_must_ge10_test` 证明比较条件等价。

$$
G_a=\{\nu:\mathrm{int}\mid\top\}\to
    \{\nu:\mathrm{int}\mid\nu\ne0\},
$$

$$
f_a=\lambda x.\lambda y.
\mathbf{if}\ y\ge10\ \mathbf{then}\ (g\,x)+1\ \mathbf{else}\ x+1.
$$

已证明：

$$
g:G_a\vdash f_a:
x:[\nu:\mathrm{int}\mid\nu=0]\to
 y:[\nu:\mathrm{int}\mid0\le\nu\le10]\mathbin{-\!*}
 [\nu:\mathrm{int}\mid\nu=1].
$$

入口为 [may_help_must_context_typed](theories/MayMustIndependentTyping.v)，
其语义推论为 `may_help_must_context_sound`。

令 $C=(g:G_a,x:[\nu=0])$，$Y=y:[0\le\nu\le10]$。
`CT_Lam`、`CT_LamD` 引入参数后得到 $C*Y$。先用 `CT_Let` 和
`CT_AppOp` 绑定比较结果 $b=(y\ge10)$，再分类整个能力：

$$
\Gamma_F=(C,y:\{\top\}),b:\mathsf{precise}(\mathsf{false}),\qquad
\Gamma_T=(C,y:\{\top\}),b:\mathsf{precise}(\mathsf{true}).
$$

$$
(C*Y),b:\mathsf{graph}(y\ge10)
\models \llbracket\Gamma_F\rrbracket\lor
         \llbracket\Gamma_T\oplus\Gamma_F\rrbracket.
$$

所有简写基础类型均为 $\mathrm{int}$，布尔绑定除外。

- $Y$ 覆盖 $y=0$，所以 false 部分必非空。$y=10$ 改走 true 分支，
  但不影响 false 分支中的 $x=0,y=0$ 见证；true 部分现在也由 $y=10$ 保证非空。
  原证明仍允许 true 部分为空，使用较弱前提即可完成推导；
  `CT_CtxCases` 区分这两种整世界情况。
- 若 $(c\times d)\sqsubseteq m$，按仅依赖 $y$ 的谓词筛选非空分支，
  有 $c\sqsubseteq m_T$、$c\sqsubseteq m_F$。
  因而从 $c\models C$ 通过 Kripke 单调性得到分支中的 $C$。
  证明保留完整闭包投影及所有额外变量，未假设普通箭头在任意子世界中稳定。
- false 分支由 $x:[\nu=0]$ 推导 `int_plus1 x` 的 $[\nu=1]$。
  true 分支以 `CT_AppFun` 使用 $g$，并推导结果 $\{\top\}$。
  两个分支都满足终止性要求。
- `CT_MatchBoth` 得到 $\{\top\}\oplus[\nu=1]$，再使用已证明的
  subtyping $\{\top\}\oplus[\nu=1]\le[\nu=1]$。
  若只有 false 分支，则使用 `CT_MatchFalseOnly`。

合并引理 `mm_sum_under_absorb` 更一般地对任意闭合整数谓词 $P$ 证明

$$
\{\nu:\mathrm{int}\mid\top\}\oplus[\nu:\mathrm{int}\mid P(\nu)]
\le [\nu:\mathrm{int}\mid P(\nu)].
$$

证明检查任意合法的新鲜结果世界，使用 Under 的同域子集向上闭包及
Kripke 单调性；终止性来自源类型的完整 guard。
它不是新增的 typing constructor。

独立箭头有实质作用：取 $g=\lambda i.1$ 和相关能力

$$
\{(x=0,y=11)\}\cup\{(x=1,y=k)\mid0\le k\le10\}.
$$

两个边缘覆盖都成立，但程序始终返回 $2$。普通逗号无法提供乘积配对保证。
该反例另在 [MayMustRelationalChecks.v](experiments/MayMustRelationalChecks.v)
中检查；完整 typing 证明使用项目实际的 `WfWorld` 和求值语义。

## 例 (b)：Must-analysis helps may-analysis

$$
G_b=
(\{\nu:\mathrm{int}\mid\top\}\to\{\nu:\mathrm{int}\mid\nu>0\})
\sqcap
([\nu:\mathrm{int}\mid\top]\to[\nu:\mathrm{int}\mid\nu>0]),
$$

$$
f_b=\lambda x.\mathbf{let}\ a=g\,x\ \mathbf{in}\
\mathbf{if}\ a>3\ \mathbf{then}\ 5\ \mathbf{else}\ 2.
$$

已证明：

$$
g:G_b\vdash f_b:
x:[\nu:\mathrm{int}\mid\top]\to
(\{\nu:\mathrm{int}\mid\nu=2\}\oplus
 \{\nu:\mathrm{int}\mid\nu=5\}).
$$

入口为 [must_help_may_context_typed](theories/MayMustTyping.v)，
其语义推论为 `must_help_may_context_sound`。

`typing_inter_r` 取出 must 箭头，`CT_AppFun` 推导 $g\,x:[\nu>0]$。
绑定 $a$ 及比较结果 $b=(a>3)$ 后，正数覆盖提供 $a=1,4$ 的见证，
因此 $b$ 的 true/false 两部分均非空。
`CT_CtxSub` 转为仅声明精确布尔绑定的和上下文，后续不再使用 $g,x,a$。
`CT_MatchBoth` 给出 $\{\nu=5\}\oplus\{\nu=2\}$，最后用和的交换
subtyping 得到论文中的顺序。Under 允许的额外非正结果也由布尔图正确分类。

该目标要求两类结果都存在，不能用单一 Over $\{\nu=2\lor\nu=5\}$ 代替。
覆盖是整个能力上的结论，不是每个固定 $x$ 都返回两者。

## 原生整数和证明文件

依用户选择，增加了 `TInt`、`cint : Z -> constant` 和两个整数原语：

$$
\mathsf{int\_plus1}:\mathrm{int}\to\mathrm{int},\qquad
\mathsf{int\_gt}_k:\mathrm{int}\to\mathrm{bool}.
$$

运行规则分别返回 $z+1$ 和 $\mathsf{Z.gtb}(z,k)$，允许负数输入。
已扩展基本类型、运行语义、canonical forms 和 `concrete_Φ` 的精确原语图，
并通过原有 primitive soundness 证明接入 Fundamental。
整数的递归度量取 $|z|$；这两个例子均无递归，不使用该度量或 T-Fix。
原有自然数算术、Tree/List、类型指称和 `CT_Fix` 保留。

| 文件 | 内容 |
|---|---|
| `MayMustRevised.v` | 两个整数程序、论文规约、良构与基本 typing |
| `MayMustWorlds.v` | 非空世界筛选、和分割、乘积筛选及精确左投影 |
| `MayMustBase.v` | 闭合整数 refinement 的覆盖与逐环境性质 |
| `MayMustPrimitives.v` | 现有 `CT_AppOp` 的整数实例及比较图 |
| `MayMustBoolCases.v` | 双布尔覆盖和上下文 subtyping |
| `MayMustTyping.v` | 例 (b) 的完整 typing 和 soundness |
| `MayMustUnder.v` | 加一的 Under 后果，使用现有 `CT_Sub` |
| `MayMustAbsorption.v` | 结果和到 Under 的派生 subtyping |
| `MayMustIndependentCases.v` | 例 (a) 的完整世界分类及闭包投影证明 |
| `MayMustIndependentTyping.v` | 例 (a) 的完整 typing 和 soundness |

**没有新增类型规则，没有 `Admitted` 或新公理。**
`Print Assumptions` 只列出项目已有的经典逻辑、indefinite description、
函数/命题外延性和 proof irrelevance。
旧 `MayMust.v` 保留为旧版自然数规约，不作为新版例子的证明入口。

## 与 Gemini 的讨论及独立核查

2026-10-18，经用户提供的新供应商，使用精确模型 `gemini-4-argon`
完成五轮讨论。供应商生成探测成功后，等待自动化已暂停。
请求和回复保留在本机临时目录，密钥未写入项目或讨论文件。

1. 第一、二轮核对两个函数规约和不同箭头，排除了参数覆盖等同于逐输入覆盖
   的误读。例 (a) 的非零输出及例 (b) 的 Over 正数分量，对这里证明的最终
   目标都可弱化；实现仍保留论文原规约。
2. Gemini 曾提出额外变量会破坏乘积筛选的反例，第三轮撤回。
   实际 `WfWorld` 证明允许兼容的重叠域和相关额外变量；未限制世界必须紧致。
3. 第四轮确认例 (b) 可在绑定比较结果后隐藏其余变量，并指出例 (a) 应在
   `CT_Let` **之后**分类，避免使用未经证明的逗号对 $\oplus$ 分配律。
4. 第五轮讨论进一步简化：分支只需保留 $C$、$y$ 的基本 Over 和精确布尔值，
   无需继续维护 $y$ 的完整 Under 或另造 $(y,b)$ 独立因子。此路线已实际实现。
5. Gemini 对结果合并给出的规范结果世界路线只作为建议。
   最终 Rocq 证明直接检查任意结果扩展；终止性使用源类型的 guard，
   没有采用回复中后附的反向投影表述，也没有把模型赞同当作验证结果。

构建命令：

```sh
opam exec -- rocq makefile -f _CoqProject -o Makefile
opam exec -- make -j6
```

以上完整构建已通过，包含原有自然数算术和 BST 证明；独立的关系反例检查
也已编译通过。`git diff --check` 无错误。
