# Example 3.3：为什么递归体前提不成立

分析对象：论文 *Context Types: Bunched Modalities for Unifying Safety and
Reachability*（2026 年 7 月版）第 12 页 Example 3.3，以及第 10 页 T-Fix
和第 14–17、21 页的世界、逻辑与类型语义。论文与项目实现的对应关系见
[语义审查](SemanticsAudit.md)。

## 待检查的是哪条 judgement

论文第 12 页 Example 3.3 的减法程序及目标类型为：

$$
\begin{aligned}
&\mathbf{fix}\;\mathrm{sub}.\lambda x.\lambda y.\;
  \mathbf{if}\;x=0\;\mathbf{then}\;0\;\mathbf{else}\;
  \mathbf{if}\;y=0\;\mathbf{then}\;x\;\mathbf{else}\;
  \mathrm{sub}\,(x-1)\,(y-1)
\\[-1pt]
&\quad : x:\{\nu:\mathrm{nat}\mid\top\}\to
  y:[\nu:\mathrm{nat}\mid\nu\le x]\to
  [\nu:\mathrm{nat}\mid\nu\le x].
\end{aligned}
$$

记当前参数为 $x$，下一次递归的参数为 $u$，避免原文的同名绑定混淆。
递归假设的类型记为：

$$
R_x =
u:\{\nu:\mathrm{nat}\mid\nu<x\}\to
v:[\nu:\mathrm{nat}\mid\nu\le u]\to
[\nu:\mathrm{nat}\mid\nu\le u].
$$

“According to T-Fix, we need to show that” 后的公式相应为：

$$
\begin{aligned}
&x:\{\nu:\mathrm{nat}\mid\top\},\quad \mathrm{sub}:R_x
\\
&\quad\vdash
\lambda y.\;
\mathbf{if}\;x=0\;\mathbf{then}\;0\;\mathbf{else}\;
\mathbf{if}\;y=0\;\mathbf{then}\;x\;\mathbf{else}\;
\mathrm{sub}\,(x-1)\,(y-1)
\\
&\qquad : y:[\nu:\mathrm{nat}\mid\nu\le x]\to
[\nu:\mathrm{nat}\mid\nu\le x].
\end{aligned}
$$

**这条公式正确列出了 T-Fix 的证明义务；问题是它作为开放 typing judgement，
在正文给出的语义下不能成立。** 以下给出满足其上下文、却不满足结论的世界。

## 为什么可以用恒零函数解释递归变量

实际执行时，展开不动点确实会把 `sub` 替换为整个递归函数本身。
但上述前提是在检查开放递归体：上下文只假设 $\mathrm{sub}:R_x$，没有附加
“$\mathrm{sub}$ 等于最终不动点”的等式。根据开放 judgement 的 soundness，
结论必须对每个满足上下文的世界成立，包括其中任何满足 $R_x$ 的递归变量解释。

因此，选择恒零函数并不是改变实际程序的运行语义，而是在检验这个前提的全称要求。
它能否构成反例，取决于它是否满足所选世界上的 $R_x$；不能仅凭它不是实际的
递归函数就将其排除。

## 满足上下文的混合世界

取基本类型正确且终止的函数，以及非空、同域的世界：

$$
\begin{aligned}
f_0 &= \lambda u.\lambda v.\,0,\\
r &= \{[x\mapsto0,\mathrm{sub}\mapsto f_0],
        [x\mapsto2,\mathrm{sub}\mapsto f_0]\}.
\end{aligned}
$$

两个环境都满足 $x:\{\nu:\mathrm{nat}\mid\top\}$。下面检查递归假设。
若 $r\sqsubseteq r'$，$r'$ 在旧变量上的投影必须恰好为 $r$，因此一定保留
至少一个 $x=0$ 的环境扩展。在任何继续绑定自然数实参 $u$ 的扩展中，
输入的 Over 规约都要求该环境满足 $u<0$，这是不可能的。

所以，在 $r$ 及其 Kripke 扩展上，递归箭头都没有满足输入规约的实参扩展。
其“输入满足规约则应用满足输出规约”的行为要求真空成立，因而：

$$
r\models \mathrm{sub}:R_x.
$$

这里的空域是整个混合世界上的输入要求；固定 $x=2$ 时，$u<x$ 本身当然有解。
$f_0$ 的基本类型与终止性也没有问题，因而相关 guard 不能排除这个解释。
第 21 页先绑定函数求值结果的广义箭头定义同样不能排除它：$f_0$ 是确定的函数值。

## 结论的 Under 覆盖失败

对结论中的 $\lambda y$，选择保留旧世界投影的实参扩展：

$$
s=\{[x\mapsto a,\mathrm{sub}\mapsto f_0,y\mapsto b]
       \mid(a,b)\in\{(0,0),(2,0),(2,1),(2,2)\}\}.
$$

$s$ 在旧变量上的投影为 $r$。固定 $x=0$ 时，$y$ 覆盖 $\{0\}$；
固定 $x=2$ 时，$y$ 覆盖 $\{0,1,2\}$。所以它满足输入的 Under 规约
$y:[\nu:\mathrm{nat}\mid\nu\le x]$。

将递归变量解释为 $f_0$ 后，递归体的结果为：

| $x$ | $y$ | 结果 |
| --- | --- | --- |
| 0 | 0 | 0 |
| 2 | 0 | 2 |
| 2 | 1 | 0 |
| 2 | 2 | 0 |

在 $x=2$ 的纤维中，输出只有 $\{0,2\}$，缺少规约要求覆盖的 $1$。
因此该实参满足输入类型，而应用不满足输出类型
$[\nu:\mathrm{nat}\mid\nu\le x]$。结论的箭头类型失败，构成上述开放
judgement 的反模型。

## 原文分支论证缺少哪一步

原文随后认为：当 $x>0$ 时，$x-1$ 是满足严格递减约束的合法递归实参。
在只含正数参数的世界里，这个算术事实成立；但应用类型规则还需要递归函数
在这个分支世界中仍具有 $R_x$。

从 $r$ 筛出 $x=2$ 的世界，记为 $r_2$，则：

$$
r_2=\{[x\mapsto2,\mathrm{sub}\mapsto f_0]\},\qquad
r_2\subseteq r,\qquad r\not\sqsubseteq r_2.
$$

筛选删除了旧环境，不是 Kripke 扩展，所以不能由单调性把 $R_x$ 从 $r$ 传递给
$r_2$。本例也直接说明该传递不成立：在 $r_2$ 中取 $u=1$，再让 $v$ 覆盖
$0,1$，$f_0\,u\,v$ 只返回 $0$，无法覆盖 $R_x$ 要求的 $0,1$。

因此，缺失的不是 $x-1<x$ 的算术证明，而是**递归假设从混合世界传到分支世界
所需的局部化性质**。正文给出的普通箭头没有提供这一性质。

## 结论及验证范围

- 反例针对 Example 3.3 所列的递归体前提；“根据 T-Fix 需要证明这个前提”
  这一步本身正确。
- 它不反驳 T-Fix 的 soundness：规则要求先证明前提，而本例恰好无法满足这个要求。
  它也不反驳实际闭合减法函数的计算正确性或其目标语义规约。
- [已由 Rocq 证明的关键引理](../ContextTyping/theories/SoundnessFixSelf.v#L378)
  是 `fix_rec_arg_impossible_at_min_zero`，即零最小度量导致严格递减实参不存在。
  上面的完整反模型仍是数学推演，尚未编码成 Rocq 定理。
- 后续 add/sub、BST 的 typing 采用其他已证明 sound 的规则构造，绕开了这个前提；
  这些成果没有补成 Example 3.3 原文的这一步推导。

该结论依据给定的 2026 年 7 月版 PDF 正文。若另有补充材料规定更强的递归假设
或局部化语义，需要据其重新检查，不能从本文推断其内容。
