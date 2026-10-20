# 案例证明新增的类型规则

共新增 **9 条 context typing 原始规则**：变量支持 2 条、算术准备 4 条、BST 组合 2 条、独立箭头引入 1 条。下式按案例中的空外部环境书写，省略固定原语环境。

记号沿用论文 Fig. 2、Fig. 4、§4.1–4.4 和 Fig. 7：

- Over：$\{\nu:b\mid\phi\}$；Under：$[\nu:b\mid\phi]$；精确类型直接写两者的交 $\sqcap$。
- 值直接作为表达式：代码的 `ret v` 写作 $v$；`tapp_tm (ret v) x` 经确定性 let 化简写作 $v\,x$。箭头采用命名依赖参数 $x:\tau_x\to\tau$。
- $\llbracket\Gamma\rrbracket$ 省略空下标；类型指称写作 $\llbracket\tau\rrbracket_{\lfloor\Gamma\rfloor}e$；$r$ 表示 capability，$\sigma$ 表示环境。

与论文 Fig. 4 一样，所有规则省略以下静态侧条件：

$$
\varnothing\vdash^{\mathrm{WF}}\Gamma,
\qquad
\lfloor\Gamma\rfloor\vdash^{\mathrm{WF}}\tau,
\qquad
\lfloor\Gamma\rfloor\vdash_s e:\lfloor\tau\rfloor.
$$

## Context typing 规则

### 1. [CT_VarR](../ContextTyping/theories/Typing.v#L246)：依赖变量读取

$$
\frac{}{\Gamma,x:\tau\vdash x:\tau}
$$

$\tau$ 可以依赖前缀 $\Gamma$。

### 2. [CT_VarSelf](../ContextTyping/theories/Typing.v#L252)：变量精确化

$$
\frac{}{\Gamma\vdash x:
\{\nu:b\mid\nu=x\}\sqcap[\nu:b\mid\nu=x]}
$$

### 3. [CT_CtxCases](../ContextTyping/theories/Typing.v#L261)：有限上下文分类

$$
\frac{
  \forall i\in\{1,\ldots,n\}.\;
    \lfloor\Gamma_i\rfloor=\lfloor\Gamma\rfloor
    \;\land\;\Gamma_i\vdash e:\tau
  \qquad
  \llbracket\Gamma\rrbracket\models
    \bigvee_{i=1}^{n}\llbracket\Gamma_i\rrbracket
}{\Gamma\vdash e:\tau}
$$

$\vee$ 是逻辑析取；最终 add/sub 与 BST 推导未调用此规则。

### 4. [CT_Conv](../ContextTyping/theories/Typing.v#L271)：项等价转换

$$
\frac{
  \begin{gathered}
  \Gamma\vdash e_1:\tau
  \\
  \forall r\models\llbracket\Gamma\rrbracket.\;
  \forall\sigma\in r.\;
  \left\{
  \begin{aligned}
  &\forall v.\;
    \sigma(e_1)\hookrightarrow^{*}v
    \Longleftrightarrow\sigma(e_2)\hookrightarrow^{*}v,\\
  &\operatorname{Total}(\sigma(e_1))
    \Longleftrightarrow\operatorname{Total}(\sigma(e_2)).
  \end{aligned}
  \right.
  \end{gathered}
}{\Gamma\vdash e_2:\tau}
$$

$\sigma(e)$ 表示闭合代入；$\hookrightarrow^{*}$ 与 $\operatorname{Total}$ 沿用论文的求值和 guard 记号，后者在实现中对应 must termination。

### 5. [CT_ArrowIntro](../ContextTyping/theories/Typing.v#L281)：从应用引入值的箭头

$$
\frac{
  \Gamma,x:\{\nu:b\mid\phi\}\vdash v\,x:\tau
}{\Gamma\vdash v:x:\{\nu:b\mid\phi\}\to\tau}
\qquad(x\text{ fresh})
$$

$\tau$ 中的 $x$ 由箭头绑定，对应代码的 `cty_open 0 x τ`；前提按任意新鲜 $x$ 检查。

### 6. [CT_WandIntro](../ContextTyping/theories/Typing.v#L291)：从应用引入值的独立箭头

$$
\frac{
  \Gamma*x:\tau_x\vdash v\,x:\tau
}{\Gamma\vdash v:x:\tau_x\mathbin{-\!*}\tau}
\qquad(x\text{ fresh})
$$

$v$ 为值，$\varnothing\vdash^{\mathrm{WF}}\tau_x$；结果 $\tau$ 可依赖 $x$。
应用前提必须有实际 typing 推导。soundness 由
[fundamental_value_wand_case](../ContextTyping/theories/SoundnessWandIntro.v)
证明并接入 `Fundamental`；原始 merge worker 使用此规则，无需 η 包装。

### 7. [CT_FiberCases](../ContextTyping/theories/Typing.v#L301)：纤维分类

使用论文 Definition 4.2 的 $\operatorname{Fib}$，推广到变量集合上的投影环境：

$$
\operatorname{Fib}(r,\sigma)
=\{\rho\in r\mid\rho|_{\operatorname{dom}(\sigma)}=\sigma\},
\qquad \sigma\in r|_X.
$$

展开纤维覆盖和组合性前提，规则为：

$$
\frac{
  \begin{gathered}
  \forall i\in I.\;
    \lfloor\Gamma_i\rfloor=\lfloor\Gamma\rfloor
    \;\land\;\Gamma_i\vdash e:\tau
  \\
  \forall r\models\llbracket\Gamma\rrbracket.\;
  \forall\sigma\in r|_X.\;
    \exists i\in I.\;
    \operatorname{Fib}(r,\sigma)\models\llbracket\Gamma_i\rrbracket
  \\
  \forall r.\;
  \left(
    \forall\sigma\in r|_X.\;
    \operatorname{Fib}(r,\sigma)\models
      \llbracket\tau\rrbracket_{\lfloor\Gamma\rfloor}e
  \right)
  \Longrightarrow
  r\models\llbracket\tau\rrbracket_{\lfloor\Gamma\rfloor}e
  \end{gathered}
}{\Gamma\vdash e:\tau}
$$

$I$ 可以无限。最后一项必须单独证明；此处保留完整纤维公式，论文的 $X\mathbin{\triangleright}P$ 还包含对 $P$ 的赋值代换。

### 8. [CT_ChooseUnder](../ContextTyping/theories/Typing.v#L313)：选择的覆盖

$$
\frac{
  \Gamma\vdash e_L:\{\nu:b\mid\top\}
  \qquad
  \Gamma\vdash e_R:[\nu:b\mid\phi]
}{\Gamma\vdash e_L\oplus e_R:[\nu:b\mid\phi]}
$$

项中的 $\oplus$ 沿用论文 Fig. 7 的非确定选择记号，对应 `choose_tm`。右分支提供覆盖，两分支均须终止。

### 9. [CT_NodeUnderGraph](../ContextTyping/theories/Typing.v#L321)：条件节点覆盖

$$
\frac{
  \begin{gathered}
  \Gamma\vdash x_p:[\nu:\mathsf{nat}\mid\phi_P]
  \qquad
  \Gamma\vdash x_k:\{\nu:\mathsf{nat}\mid\phi_K\}
  \\
  \Gamma\vdash x_l:[\nu:\mathsf{nat}\;\mathsf{tree}\mid\phi_L]
  \qquad
  \Gamma\vdash x_r:[\nu:\mathsf{nat}\;\mathsf{tree}\mid\phi_R]
  \end{gathered}
}{\Gamma\vdash\mathsf{Node}\;x_k\;x_l\;x_r:
  [\nu:\mathsf{nat}\;\mathsf{tree}\mid\Theta]}
$$

此规则另要求以下三组侧条件，由 [node_under_graph_spec](../Denotation/theories/TreeCoverage.v#L76) 展开，并以对应 qualifier 的满足条件消去桥接谓词 $P,K,L,R,Q$。

**依赖与新鲜性。** 沿用论文 $\mathrm{FV}$ 表示 qualifier 的语法依赖：

$$
\begin{aligned}
\mathrm{FV}(\phi_P)\setminus\{\nu\}
  =\mathrm{FV}(\Theta)\setminus\{\nu\}&=S,\\
\mathrm{FV}(\phi_K)\setminus\{\nu\}
  =\mathrm{FV}(\phi_L)\setminus\{\nu\}&=S\cup\{x_p\},\\
\mathrm{FV}(\phi_R)\setminus\{\nu\}&=S\cup\{x_p,x_l\},\\
x_p\notin S,\quad x_k,x_l\notin S\cup\{x_p\},\quad
x_r&\notin S\cup\{x_p,x_l\}.
\end{aligned}
$$

代码允许声明谓词未使用的支持变量；用论文语法表示时，补入 $z=z$ 保留该变量的出现。例如 BST 的右子树规约在此写法中要补入 $x_l=x_l$，以保持对已选左子树的条件覆盖；这个恒真项不能在计算 $\mathrm{FV}$ 时删去。

**目标分解与根值确定。** 下式在 $S$ 上任意参数赋值下有效；$p,k,k'$ 取自然数，$l,r,t$ 取自然数树：

$$
\models\forall t.\;
\Theta[\nu\mapsto t]\Rightarrow
\exists p,k,l,r.\;
\begin{aligned}[t]
&t=\mathsf{Node}\;k\;l\;r\;\land\;\phi_P[\nu\mapsto p]\\
&\land\;\phi_L[x_p\mapsto p,\nu\mapsto l]\\
&\land\;\phi_R[x_p\mapsto p,x_l\mapsto l,\nu\mapsto r]\\
&\land\;\forall k'.\;
  \bigl(\phi_K[x_p\mapsto p,\nu\mapsto k']\Rightarrow k'=k\bigr).
\end{aligned}
$$

**目标存在性。** 同样对 $S$ 上任意参数赋值要求：

$$
\models\exists t:\mathsf{nat}\;\mathsf{tree}.\;
\Theta[\nu\mapsto t].
$$

上述八条规则的 soundness 均已证明并接入 [Fundamental](../ContextTyping/theories/Soundness.v#L1044)。本节是对应实现的论文记号表述；没有更改 `CT_Fix` 或指称语义。

## 准备阶段引入的 Tree/List 基础规则

以下四条属于 [基础类型判断](../CoreLang/theories/BasicTyping.v#L71)，沿用论文的 $\Sigma\vdash_s e:s$；匹配分支采用新鲜绑定变量。

$$
\frac{
  \Sigma\vdash_s k:\mathsf{nat}\qquad
  \Sigma\vdash_s l:\mathsf{nat}\;\mathsf{tree}\qquad
  \Sigma\vdash_s r:\mathsf{nat}\;\mathsf{tree}
}{\Sigma\vdash_s\mathsf{Node}\;k\;l\;r:\mathsf{nat}\;\mathsf{tree}}
\;\text{(TT\_TreeNode)}
$$

$$
\frac{
  \begin{gathered}
  \Sigma\vdash_s v:\mathsf{nat}\;\mathsf{tree}\qquad
  \Sigma\vdash_s e_{\mathrm{leaf}}:s\\
  \Sigma,k:\mathsf{nat},l:\mathsf{nat}\;\mathsf{tree},r:\mathsf{nat}\;\mathsf{tree}
    \vdash_s e_{\mathrm{node}}:s
  \end{gathered}
}{\Sigma\vdash_s
  \mathbf{match}\ v\ \mathbf{with}\
  \mathsf{Leaf}\to e_{\mathrm{leaf}}\mid
  \mathsf{Node}\ k\ l\ r\to e_{\mathrm{node}}:s}
\;\text{(TT\_TreeMatch)}
$$

$$
\frac{
  \Sigma\vdash_s h:\mathsf{nat}\qquad
  \Sigma\vdash_s t:\mathsf{nat}\;\mathsf{list}
}{\Sigma\vdash_s\mathsf{Cons}\;h\;t:\mathsf{nat}\;\mathsf{list}}
\;\text{(TT\_ListCons)}
$$

$$
\frac{
  \begin{gathered}
  \Sigma\vdash_s v:\mathsf{nat}\;\mathsf{list}\qquad
  \Sigma\vdash_s e_{\mathrm{nil}}:s\\
  \Sigma,h:\mathsf{nat},t:\mathsf{nat}\;\mathsf{list}\vdash_s e_{\mathrm{cons}}:s
  \end{gathered}
}{\Sigma\vdash_s
  \mathbf{match}\ v\ \mathbf{with}\
  \mathsf{Nil}\to e_{\mathrm{nil}}\mid
  \mathsf{Cons}\ h\ t\to e_{\mathrm{cons}}:s}
\;\text{(TT\_ListMatch)}
$$

逻辑变量环境中有对应的四条 `BTT_*` 规则，见 [BasicTypingFormula.v](../ContextBasicDenotation/theories/BasicTypingFormula.v#L85)。
