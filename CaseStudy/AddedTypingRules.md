# BST 与算术证明新增的类型规则

共新增 **8 条 context typing 原始规则**：变量支持 2 条、算术准备 4 条、BST 组合 2 条。以下省略固定的原语环境和外部类型环境。

记 $O_b(\phi)$ 为 Over 类型，$U_b(\phi)$ 为 Under 类型，$P_b(\phi)=O_b(\phi)\sqcap U_b(\phi)$ 为精确类型；$\Gamma,x:\tau$ 表示加性上下文扩展。**所有规则均要求结论满足 `context_typing_wf`**（上下文与类型良构、擦除后有基础类型），公式中统一省略。

## Context typing 规则

### 1. [CT_VarR](../ContextTyping/theories/Typing.v#L246)：依赖变量读取

$$
\frac{}{\Gamma,x:\tau\vdash\operatorname{ret}x:\tau}
$$

$\tau$ 可以依赖前缀 $\Gamma$ 中的变量。

### 2. [CT_VarSelf](../ContextTyping/theories/Typing.v#L252)：变量精确化

$$
\frac{}{\Gamma\vdash\operatorname{ret}x:P_b(\nu=x)}
$$

良构条件保证 $x$ 的基础类型为 $b$。

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

每个原世界整体满足某个分支上下文。此规则已加入系统，最终 add/sub 与 BST 推导未调用它。

### 4. [CT_Conv](../ContextTyping/theories/Typing.v#L271)：项等价转换

$$
\frac{
  \Gamma\vdash e_1:\tau
  \qquad
  \forall m\models\llbracket\Gamma\rrbracket.\;
    e_1\equiv_m^{\mathrm{res,tot}}e_2
}{\Gamma\vdash e_2:\tau}
$$

$\equiv_m^{\mathrm{res,tot}}$ 要求在 $m$ 的每个 store 上，结果集合与 must termination 均等价。

### 5. [CT_ArrowIntro](../ContextTyping/theories/Typing.v#L281)：从应用引入值的箭头

$$
\frac{
  \forall x\notin L.\;
  \Gamma,x:O_b(\phi)\vdash
    \operatorname{app}(\operatorname{ret}v,x):\tau[x]
}{\Gamma\vdash\operatorname{ret}v:O_b(\phi)\to\tau}
$$

$L$ 为有限排除集；$\tau[x]$ 打开依赖参数。结论限于值，输入限于基础 Over；每个应用须有 typing 推导。

### 6. [CT_FiberCases](../ContextTyping/theories/Typing.v#L291)：纤维分类

$$
\frac{
  \begin{gathered}
  \forall i\in I.\;
    \lfloor\Gamma_i\rfloor=\lfloor\Gamma\rfloor
    \;\land\;\Gamma_i\vdash e:\tau
  \\
  \operatorname{Join}_X\!\left(\llbracket\tau,e\rrbracket_\Gamma\right)
  \\
  \forall m\models\llbracket\Gamma\rrbracket.\;
  \forall\sigma,m_f.\;
    \operatorname{Fiber}_X(m,\sigma,m_f)
    \Rightarrow\exists i\in I.\;m_f\models\llbracket\Gamma_i\rrbracket
  \end{gathered}
}{\Gamma\vdash e:\tau}
$$

$I$ 可以无限；$\operatorname{Fiber}_X$ 表示固定 $X$ 上赋值的纤维。组合性是显式前提：

$$
\operatorname{Join}_X(P)\;\Longleftrightarrow\;
\forall m.\;
\left(\forall\sigma,m_f.\;
\operatorname{Fiber}_X(m,\sigma,m_f)\Rightarrow m_f\models P\right)
\Rightarrow m\models P.
$$

### 7. [CT_ChooseUnder](../ContextTyping/theories/Typing.v#L303)：选择的 Under 覆盖

$$
\frac{
  \Gamma\vdash e_L:O_b(\top)
  \qquad
  \Gamma\vdash e_R:U_b(\phi)
}{\Gamma\vdash\operatorname{choose}(e_L,e_R):U_b(\phi)}
$$

右分支提供覆盖，左分支允许额外结果；两分支均须终止。用于组合 BST 的 Leaf 与生成分支。

### 8. [CT_NodeUnderGraph](../ContextTyping/theories/Typing.v#L311)：条件节点覆盖

$$
\frac{
  \begin{gathered}
  \Gamma\vdash\operatorname{ret}x_p:U_{\mathsf{nat}}(\phi_P)
  \qquad
  \Gamma\vdash\operatorname{ret}x_k:O_{\mathsf{nat}}(\phi_K)
  \\
  \Gamma\vdash\operatorname{ret}x_l:U_{\mathsf{tree}}(\phi_L)
  \qquad
  \Gamma\vdash\operatorname{ret}x_r:U_{\mathsf{tree}}(\phi_R)
  \\
  \mathcal G(S,x_p,x_k,x_l,x_r,\phi_P,\phi_K,\phi_L,\phi_R,\Theta;P,K,L,R,Q)
  \end{gathered}
}{\Gamma\vdash\operatorname{Node}(x_k,x_l,x_r):U_{\mathsf{tree}}(\Theta)}
$$

$\mathcal G$ 是 [node_under_graph_spec](../Denotation/theories/TreeCoverage.v#L76)：要求新鲜性、规约关系、目标分解、根值唯一性及目标存在性。其支持集满足：

$$
\begin{aligned}
\operatorname{dom}(\phi_P)=\operatorname{dom}(\Theta)&=S,\\
\operatorname{dom}(\phi_K)=\operatorname{dom}(\phi_L)&=S\cup\{x_p\},\\
\operatorname{dom}(\phi_R)&=S\cup\{x_p,x_l\}.
\end{aligned}
$$

右子树覆盖保留已选左子树 $x_l$，保证左右结果可共同实现。

上述八条规则的 soundness 均已证明并接入 [Fundamental](../ContextTyping/theories/Soundness.v#L1044)。`CT_Fix` 保持原定义；weakening、交类型投影和持久变量消去均为派生规则。

## 准备阶段引入的 Tree/List 基础规则

以下四条属于 [STLC 基础类型判断](../CoreLang/theories/BasicTyping.v#L71)，用 $\vdash_b$ 表示；分支中的绑定变量均取新鲜变量。

$$
\frac{
  \Gamma\vdash_b k:\mathsf{nat}\qquad
  \Gamma\vdash_b l:\mathsf{tree}\qquad
  \Gamma\vdash_b r:\mathsf{tree}
}{\Gamma\vdash_b\operatorname{Node}(k,l,r):\mathsf{tree}}
\;\text{(TT\_TreeNode)}
$$

$$
\frac{
  \Gamma\vdash_b v:\mathsf{tree}\qquad
  \Gamma\vdash_b e_{\mathrm{leaf}}:T\qquad
  \Gamma,k:\mathsf{nat},l:\mathsf{tree},r:\mathsf{tree}
    \vdash_b e_{\mathrm{node}}:T
}{\Gamma\vdash_b\operatorname{matchTree}(v,e_{\mathrm{leaf}},(k,l,r).e_{\mathrm{node}}):T}
\;\text{(TT\_TreeMatch)}
$$

$$
\frac{
  \Gamma\vdash_b h:\mathsf{nat}\qquad
  \Gamma\vdash_b t:\mathsf{list}
}{\Gamma\vdash_b\operatorname{Cons}(h,t):\mathsf{list}}
\;\text{(TT\_ListCons)}
$$

$$
\frac{
  \Gamma\vdash_b v:\mathsf{list}\qquad
  \Gamma\vdash_b e_{\mathrm{nil}}:T\qquad
  \Gamma,h:\mathsf{nat},t:\mathsf{list}\vdash_b e_{\mathrm{cons}}:T
}{\Gamma\vdash_b\operatorname{matchList}(v,e_{\mathrm{nil}},(h,t).e_{\mathrm{cons}}):T}
\;\text{(TT\_ListMatch)}
$$

逻辑变量环境中有对应的四条 `BTT_*` 规则，见 [BasicTypingFormula.v](../ContextBasicDenotation/theories/BasicTypingFormula.v#L85)。
