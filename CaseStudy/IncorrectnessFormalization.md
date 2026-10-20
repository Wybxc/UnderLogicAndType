# Revised pp.24–25：Incorrectness reasoning

依据用户提供的 revised `main(1).pdf`，Fig.8 及第24–25页。采用论文记号：
$\{\nu:b\mid\phi\}$ 为 Over，$[\nu:b\mid\phi]$ 为 Under，
$\to$ 为 entangled arrow，$-\!*$ 为 independent arrow。

## 已证明的类型

令 $S(\nu)=\operatorname{sorted}(\nu)$，$R$ 为 Fig.8 错误 merge 的精确结果函数。
`IncorrectMerge.merge_value` 是实际的 `vfix` 递归 worker，已证明

$$
\vdash \mathit{worker}:
x:\{\nu:\mathrm{nat\ list}\mid\top\}\to
 y:\{\nu:\mathrm{nat\ list}\mid\top\}\to
 \bigl(\{\nu:\mathrm{nat\ list}\mid\nu=R(x,y)\}
       \sqcap[\nu:\mathrm{nat\ list}\mid\nu=R(x,y)]\bigr).
$$

入口：`merge_worker_precise_context_typed`，见
[MergeTraceTyping.v](theories/MergeTraceTyping.v)。此类型还包含逐输入的精确可达性，
输入域也覆盖全部列表，强于论文所需的 sorted-input Over 图规约。

同一个 worker 还满足论文第25页的有限轨迹类型：

$$
\vdash \mathit{worker}:
x:\{\nu:\mathrm{nat\ list}\mid S(\nu)\}\to
 y:\{\nu:\mathrm{nat\ list}\mid S(\nu)\}\to
 \{\nu:\mathrm{nat\ list}\mid\Phi(x,y,\nu)\},
$$

$$
\begin{aligned}
\Phi(x,y,\nu)={}&(x=[]\land y=[]\Rightarrow\nu=[])\\
 &\land(x=[2]\land y=[4]\Rightarrow\nu=[2;4])\\
 &\land(x=[1;2]\land y=[3;4]\Rightarrow\nu=[1;3;2;4]).
\end{aligned}
$$

入口：`merge_worker_trace_context_typed`。`merge_trace_sum_subtype` 还独立证明：
在下面的独立输入上下文中，仅此有限轨迹规约就足以推出错误结果的 sum 类型。

$$
\Gamma=(\varnothing*x:[\nu:\mathrm{nat\ list}\mid S(\nu)])
                    *y:[\nu:\mathrm{nat\ list}\mid S(\nu)],
$$

$$
\Gamma\vdash\mathit{body}(x,y):
 \{\nu:\mathrm{nat\ list}\mid\neg S(\nu)\}
 \oplus\{\nu:\mathrm{nat\ list}\mid\top\}.
$$

入口：`merge_body_incorrect_context_typed`（精确图路线）、
`merge_body_trace_incorrect_context_typed`（有限轨迹路线）。

原始 `vfix` worker 直接满足完整独立箭头类型：

$$
\vdash\mathit{worker}:
x:[\nu:\mathrm{nat\ list}\mid S(\nu)]\mathbin{-\!*}
 y:[\nu:\mathrm{nat\ list}\mid S(\nu)]\mathbin{-\!*}
 \bigl(\{\nu:\mathrm{nat\ list}\mid\neg S(\nu)\}
       \oplus\{\nu:\mathrm{nat\ list}\mid\top\}\bigr).
$$

入口：`merge_worker_incorrect_context_typed`，见
[MergeWorkerTyping.v](theories/MergeWorkerTyping.v)。
以上三个闭合函数类型均有直接应用 `concrete_Fundamental` 的 `context_sound` 推论。

## 从应用引入独立箭头

新增的 `CT_WandIntro` 是 `CT_ArrowIntro` 对独立箭头的推广：

$$
\frac{
  \Gamma*x:\tau_x\vdash v\,x:\tau
}{
  \Gamma\vdash v:x:\tau_x\mathbin{-\!*}\tau
}
\qquad(x\text{ fresh}).
$$

$v$ 必须是值；沿用现有 well-formedness 条件，特别是 $\tau_x$ 闭合，
而结果 $\tau$ 可以依赖 $\Gamma$ 和参数 $x$。
前提要求真实的 `has_context_type` 应用推导，因此这是一条 syntactic typing rule。

`fundamental_value_wand_case` 在
[SoundnessWandIntro.v](../ContextTyping/theories/SoundnessWandIntro.v)
证明其 soundness，并已接入 `Fundamental`。证明在任意兼容实参世界与原世界的乘积中
构造 $\Gamma*x:\tau_x$，应用前提的 soundness，再处理函数结果变量的别名及相关环境。
函数结果绑定和 must termination guard 均保留在既有 denotation 中。

`merge_first_incorrect_context_typed` 先将原始 worker 的第一次应用，通过保留结果集与
must termination 的有限归约证书转换为它实际返回的内层 λ；内层 λ 使用 `CT_LamD`。
随后 `CT_WandIntro` 直接引入 worker 的最外层独立箭头。
程序及递归调用均使用 `IncorrectMerge.merge_value`；旧的显式 η 包装入口已移除。

## 证明路线与检查

1. [MergeProgram.v](theories/MergeProgram.v) 用现有 List 语法编码程序，比较使用
   `sub_value` 和 `op_eq0`。`merge_result_cons` 证明与图中的大小比较等价。
2. [MergeReduction.v](theories/MergeReduction.v) 对第一个列表归纳，证明实际程序到
   $R(x,y)$ 的确定性有限归约证书，同时保留 must termination。
3. [MergeTyping.v](theories/MergeTyping.v) 从 `CT_Const` 出发，用 `CT_Conv` 将证书
   转成每个固定输入的真实 `has_context_type` 推导；再用 `CT_FiberCases` 合并精确
   **基础结果类型**。`merge_graph_joinable` 显式证明 joinability，保留额外世界变量。
   归纳假设构造的是归约证书；这里没有把语义正确性直接当成任意类型推导规则。
4. `CT_Sub` 在完整输入世界中处理 sum。独立覆盖保证输入对 $([1;2],[3;4])$ 和
   $([],[])$ 都出现，分别保证错误部分与剩余部分非空。后者满足 $\{\top\}$。
   结果扩展的处理使用已有的精确投影与分支 refinement 引理。
5. `CT_LamD` 引入程序实际返回的内层独立箭头，`CT_WandIntro` 直接引入原始 worker
   的外层独立箭头。普通箭头通过 `CT_Lam`、`CT_ArrowIntro` 和行政归约转换引入。
   有限轨迹由精确图的 Over consequence 得到。

本次新增一条类型规则 `CT_WandIntro`，没有新增原语或公理，也没有修改 denotation 或 `CT_Fix`。
本证明使用“固定输入归约 + 基础类型 fiber 合并”，并未验证论文所说的直接 `T-Fix` 路线。
所有模块已加入 `_CoqProject`。统一编译与独立 `rocq check` 均通过；
`Print Assumptions` 仅列出项目已有的经典逻辑、indefinite description、
函数/命题外延性和 proof irrelevance。

第25页隐藏 bug 的相关调用关系也已核对：

$$
S(x)\land S(y)\land(x=[]\lor y=[]).
$$

`merge_masked_left_covers`、`merge_masked_right_covers` 证明两边分别覆盖所有有序列表，
`merge_masked_result_sorted` 证明其输出总有序。这部分形式化的是输入关系，
没有为论文外部的 `sorted_list_gen` 另行实现生成器及其调用程序的 context typing。

## Gemini 讨论

通过用户授权的供应商调用 `gemini-4-argon`，完成一轮讨论。采用其建议的
“精确基础图类型 → 全局 semantic subsumption”路线；具体的 joinability、
独立配对和非空 sum 义务均由 Rocq 检查。后续追问超时。
消除 η 包装所用的 `CT_WandIntro` 及其 soundness 由本地 Rocq 开发完成。

两点不能照搬讨论中的泛化说法：确定性单值输出不必然排斥所有 sum（两部分可能重叠）；
本例真正的障碍是非错误输入 fiber 无法满足 $\{\neg S\}$。
此外，项目 Over 类型含终止性 guard，不能只证明 partial correctness。
