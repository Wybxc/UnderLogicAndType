# bst_gen 的 context typing：与 Gemini 讨论后的证明路线

**当前状态（2026-10-17）：完整 typing 已证明。**
`theories/BSTGeneratorContextTyping.v` 的 `bst_gen_type_judgement_holds`
证明原始目标，`bst_gen_denotational_sound` 接入 `concrete_Fundamental`。
完整构建、假设审计与独立递归内核检查通过。以下保留历次计划及当时的验证边界；
最终完成记录见文末。

讨论基于提交 `ff5137b`，请求模型为 `gemini-4-argon`，使用用户指定的
Gemini 接口。供应商未返回 `modelVersion`，此处只记录请求模型。
专题讨论取得四轮有效答复。模型意见经过本地源码、边界例和反例复核；讨论结束时
以下新规则与证明义务尚未经过 Rocq 验证。后续实施状态见本文末节；
`bst_gen` 程序与核心语义定义保持原样。

2026-10-17 又进行了三轮复审，针对新增证明和非空条件修正路线；修订结论见
文末“新增基础后的三轮复审”。原四轮记录保留为讨论历史。

## 目标与证据范围

目标仍是 `BSTGeneratorProgram.bst_gen_type_judgement`，包含最外层 `□`。
现有事实是：规约良构、程序闭合且满足基本类型，以及 add/sub 的完整 context
typing 和新规则 `CT_Conv`、`CT_ArrowIntro`、`CT_FiberCases` 的 soundness。

生成器的结果是 **under** 类型。对 `r > 0`，额外返回 `Leaf` 或不完整树不违反
规约；应证明所有合法完整 BST 可达，并证明所有执行分支 must-terminate。
不能证明或假设“所有输出满足 `bst_spec`”。

建议保留现有 denotation 和 `CT_Fix`。以实际闭合 `bst_gen_value` 的尺寸作强归纳，
避免在本路线中依赖任意 `self` 的混合世界递归契约。这不是 `CT_Fix` 无法用于
任何其他策略的不可导出性定理。

## 纯树逻辑应先完成

令 `B(n,a,t) := bst_spec n a t`。需要证明：

- `B(0,a,t) ↔ t = tr_leaf`。
- 对 `n > 0`，合法目标树非空，且

  ```text
  B(n,a,Node k L R)
    ↔ ∃p, 1 ≤ p ≤ n ∧ k = a+p
          ∧ B(p-1,a,L) ∧ B(n-p,a+p,R).
  ```

左右尺寸 `p-1`、`n-p` 均小于 `n`；`n=1` 时唯一选择为 `p=1`，两侧均为
`Leaf`。当前闭区间 `range_ty` 允许调用 `range 1 1`。

独立有限检查在抽象递推模型中检验了 `n=0..6` 的目标覆盖，完整目标数量为
`1,1,2,5,14,42,132`。这不是 CoreLang 执行检查，也不是 Rocq 证明。

## 强归纳的语法目标

对每个 `n`，证明任意 `a` 与新鲜参数名下的真实判断：

```text
Δ(n,a) = r : precise(n), lo : precise(a), range : range_ty

Δ(n,a) ⊢ G r lo range : UTree {ν | B(r,lo,ν)}
```

`G` 始终是实际闭合的 `bst_gen_value`，归纳假设用于较小尺寸的实际调用。
其他具体上下文的实例由 `CT_CtxSub` 搬运，需证明擦除环境在观察变量上一致、
上下文投影蕴含与良构性；不能仅凭“Γ 包含几个绑定”就假设可搬运。
量化任意额外世界变量的统一性必须保留。

不要从某闭合函数 `f` 语义满足 `range_ty` 就直接假定 `ret f` 有语法 typing。
语义上的 `∀f, GoodRange(f) → ...` 可作辅助定理，但不能取代上述语法归纳。

## 覆盖必须保留条件依赖

设 `S={r,lo}`。在尺寸和下界固定的归纳步内，设计统一的中间 qualifier：

```text
ΦP(S,p)       := 1 ≤ p ≤ r
ΦK(S,p,k)     := k = lo+p
ΦL(S,p,L)     := 1 ≤ p ≤ r ∧ B(p-1,lo,L)
ΦR(S,p,L,R)   := 1 ≤ p ≤ r ∧ B(r-p,lo+p,R) ∧ L=L
```

最后一个 `L=L` 用于把左子树变量明确纳入 qualifier 的自由变量支持，不是为了
增加数学谓词内容。项目的 qualifier 记录支持集，under 的纤维划分因此不同。
`ΦP`、`ΦK` 也须按需要补齐共同支持 `S`；固定参数上的支持补齐仍须证明。

两次递归分别得到 `UTree ΦL` 和 `UTree ΦR`。仅在这两个基础结果上分类 pivot
及必要的旧变量，使用强归纳假设和 `CT_Sub`，再由 `CT_FiberCases` 合并回
**各自统一的条件类型**。最终树构造前须恢复尚未固定 pivot 的完整上下文。

关键反例：`n=2,lo=0` 时，固定 `p=1` 只能覆盖根为 1 的完整树，固定 `p=2`
只能覆盖根为 2 的完整树。两种分支都不能独自证明完整 `UBstBetween`。
`CT_FiberCases` 要求同一个目标类型，不能用它把这些不同的根条件目标直接
变成完整 BST 的覆盖。

## 候选通用构造规则：条件覆盖与确定函数图

候选名 `CT_NodeUnderGraph`；尚未加入 `Typing.v`，也未证明 soundness。
它应适用于一般树构造，不把 `bst_spec` 硬编码进规则。

`x_p,x_k,x_l,x_r` 是不同的对象语言变量，`S` 不包含它们。前提为同一 Γ 下的真实 typing：

```text
Γ ⊢ ret x_p : UNat  ΦP(S,ν)
Γ ⊢ ret x_k : ONat  ΦK(S,x_p,ν)
Γ ⊢ ret x_l : UTree ΦL(S,x_p,ν)
Γ ⊢ ret x_r : UTree ΦR(S,x_p,x_l,ν)
Γ ⊢wf Node x_k x_l x_r : UTree Θ(S,ν)
```

qualifier 的支持必须恰好是所显示的参数及结果变量，不含隐藏依赖。
另需纯一阶分解条件：对每个合法参数赋值 `s`，

```text
Θ(s,t) → ∃p0,k0,L0,R0,
  t = Node k0 L0 R0 ∧ ΦP(s,p0) ∧ ΦL(s,p0,L0)
  ∧ ΦR(s,p0,L0,R0)
  ∧ (∀k', ΦK(s,p0,k') → k'=k0).
```

候选结论为 `Γ ⊢ Node x_k x_l x_r : UTree Θ`。

soundness 的数学思路是：在非空 S 纤维内，pivot 的 under 前提提供 `p0` 的
store；左树前提在同一 `S,p0` 纤维提供 `L0`；右树前提在同一 `S,p0,L0`
纤维提供 `R0`；根的 over 函数图在最后的同一个 store 强制根为 `k0`。
然后构造目标结果。这需要证明各前提的 `relevant_env` 限制与同一原世界的纤维
一致，并展开 result-first 结果绑定、精确结果关系和 guard，
不能仅凭这段见证论证声称机器证明已完成。

只给左右树各自的边际覆盖是不够的：取根 3、左侧键 `{1,2}` 的两种形状
`L0,L1`、右侧键 `{4,5}` 的两种形状 `R0,R1`，世界仅含
`(L0,R0),(L1,R1)` 时，两侧单独的 under 覆盖成立，却缺少两个交叉组合。
带左树支持的右覆盖会排除这个世界。这个有限集合反例尚非 Rocq 反模型定理。

选择 pivot 加根函数图的方案，可复用 `range` 的 `[1,r]` 覆盖和 add 的精确图。
以实际 root 为首个覆盖变量也是可研究的替代方案，但需额外证明
`p ↔ lo+p` 的覆盖搬运及支持换名引理。

## 纤维分类的侧条件必须逐项证明

将旧 `left_tree : UTree ΦL` 替换成任意实际树常量的 precise 类型是允许研究的
分类，包括不完整树和 `Leaf`；不能保留原来的完整左树覆盖作为该纤维的假设。
在树常量固定的 case 内，向右树目标添加 `left_tree=left_tree` 不再细分该变量，
可研究相应的子类型引理；这不是一般 under 类型自动具有的支持扩充规则。

已有源码引理 `fiberwise_joinable_on_ty_denote_gas_under` 的实际前提是：

```text
lty_env_closed Σ
lc_tm e
tm_lvars e ⊆ dom(relevant_env Σ (CTUnder b φ) e)
X ⊆ lvars_fv(dom(relevant_env Σ (CTUnder b φ) e))
```

最后一项是 **X 包含于相关环境自由域**，不是相反方向，也不是单独的
`FV(φ) ⊆ X`。因此不能仅说“基础类型自然可合并”，或只证明终止性 guard 可合并。
可研究 `X_L={r,lo,pivot,left_size}`、
`X_R={r,lo,pivot,right_size,root,left_tree}`；它们与目标 qualifier、调用项的
相关环境关系仍须实际证明。`range` 可留在相关环境中而不作为分类变量。

每个 case 还需检查 WF、相同擦除环境，以及整个 case 上下文的模型覆盖：

- 被分类的基本变量改为精确常量类型。
- 留存的基础 over 算术图可使用已证的 over-variable 纤维稳定性引理。
- 不需要的旧基础 under 绑定可研究换成同擦除的 over-top，重新证明覆盖。
- `range : range_ty` 的单点投影保证应单独搬运。已有
  `ctx_bind_persist_singleton_projection` 与 `ctx_bind_persist_persistent`
  可用：任意非空子纤维仍保留同一个 range 值及同一单点投影。

不能推广成任意普通箭头、任意 under 绑定、任意 Γ 都能删 store。

## 其他桥与最终封装

1. 证明树分解与递减；证明具体上下文、支持变更和归纳假设搬运引理。
2. 用已有 `res_models_persist_elim` 研究派生子类型 `□τ <: τ`，优先复用
   `CT_Sub`，不另添原始消去规则；处理常量实参、ANF 应用及依赖绑定。
3. 证明候选树构造规则的 soundness，再接入 `Fundamental`。
4. 证明 under 选择规则或派生引理：

   ```text
   Γ ⊢ e1 : OTop(b)    Γ ⊢ e2 : Under(b,φ)
   ---------------------------------------
         Γ ⊢ choose e1 e2 : Under(b,φ)
   ```

   选择增加的结果不能通过 `CT_Conv` 搬运，因为它要求结果集合相等。
   规则必须保证两分支全部 must-terminate；左分支 `ret Leaf` 可满足 over-top。
   右分支的 range 调用总性与 pivot 边界来自精确 `range_ty`，算术使用已证 typing，
   两个递归调用均须由强归纳假设保证。
5. 最外层先对实际固定点值使用 `CT_ArrowIntro`，确定性展开后用 `CT_Lam`
   引入 `lo` 及高阶 `range`；在最内层基础树结果处分类 `(r,lo)`，最后用
   `CT_PersistIntro` 得到原始 `bst_gen_ty`。不需要一般箭头或 `□` 的合并定理。

专题讨论结束时未完成新的 Rocq 证明，也没有声称完整 `bst_gen` typing 已可导出。
上述候选的 soundness 与侧条件，应先成为下一阶段的明确验证对象。

## 实施中的修正与已验证基础

源码复核发现，上述构造规则的单向分解条件还不充分：`FUnder (FAtom q)`
要求存在非空的精确谓词世界，故目标谓词若为空，不能仅凭真空成立的
`Θ → 分解` 得出 under 结论。最终规则还必须要求每个相关参数纤维中的目标
集合有见证。BST 对任意自然数尺寸与下界都有合法目标；该事实由
`BSTSpecFacts.bst_spec_inhabited` 证明，不能对一般 qualifier 默认成立。

当前新增并通过 Rocq 的基础包括：

- `BSTSpecFacts.v`：成员界、界放宽、零尺寸、节点分解、递归尺寸递减、规约可满足性。
- `Denotation/PersistElim.v`：对任意良构类型（包括高阶箭头）的返回变量，
  消去类型级 `□`，使用新鲜结果别名和原世界投影，不假设删 store 的稳定性。
- `ContextTyping/PersistElim.v`：通过已有 `CT_CtxSub` 和 `CT_VarR`
  导出持久变量消去的语法 typing；未增加原始 typing 构造子。
- `ContextLogic/FormulaUnderAtom.v`：under 原子的非空性、覆盖消去与覆盖引入；
  形式化证明 under 空谓词不成立，补齐候选构造规则遗漏的非空条件。
- `ContextBasicDenotation/TreeCoverage.v`：同一原世界内的 pivot → 左树 → 右树
  条件覆盖链，以及最终同一 store 上的节点求值；尚非树构造 typing 的 soundness。
- `CoreLang/Choice.v`：实际 boolGen 选择表达式的结果并集，以及 must-termination
  当且仅当两个分支均 must-terminate。
- `BSTGeneratorUnfolding.v`：任意具有 range 基本类型的参数下，实际零尺寸调用
  到 `Leaf` 的有限确定性展开与逐 store 实例化。
- `BSTGeneratorTyping.v`：`Leaf` 的零尺寸规约 typing、实际 `range` 变量的
  高阶持久消去，以及实际固定点零尺寸调用的 `bst_zero_call_context_typed`。
  该定理的源推导是 `CT_Const`；通过已证的 `CT_Conv` 搬运有限展开，
  不以运行正确性作为任意 typing 的引入规则。

已运行全项目构建；上述新证明均无 `Admitted` 或新公理，已检查的证明假设
不超出既有 `Fundamental` 使用的假设。树构造与选择的完整 soundness、
正尺寸递归调用推导、最终生成器 typing 仍待完成。

## 新增基础后的三轮复审（2026-10-17）

本次仍请求 `gemini-4-argon`，由第一家用户指定的供应商取得三轮实质答复，
未更换模型。供应商未报告 `modelVersion`，故不声称独立验证了后端模型身份。
本次只修订证明计划，没有新增规则、soundness 证明或完整 BST typing。

### 节点规则先使用固定正尺寸的谓词

此前“对任意参数赋值的节点分解”还需要明确适用域：若目标直接为
`B(r,lo,t)`，任意赋值包括 `r=0`，此时合法目标是 `Leaf`，不能分解成节点。
这不否定已证的条件覆盖见证链，而是要求修正规则的接口或应用谓词。

本轮建议采用较小的接口：在元语言中固定 `n>0,a`，保留 `S={r,lo}` 的
显式支持，谓词内容用常量 `n,a`：

```text
Θ(S,t)       := B(n,a,t)
ΦP(S,p)      := 1 ≤ p ≤ n
ΦK(S,p,k)    := k = a+p
ΦL(S,p,L)    := 1 ≤ p ≤ n ∧ B(p-1,a,L)
ΦR(S,p,L,R)  := 1 ≤ p ≤ n ∧ B(n-p,a+p,R)
```

这些表达式的支持仍分别为 `S`、`S`、`S∪{p}`、`S∪{p}`、`S∪{p,L}`，
每个 qualifier 另含结果绑定变量 `ν`。特别是右侧的支持必须含 `L`，即使
谓词正文不使用它；这要求按每个实际左树值分别覆盖右树。
支持集是记录的一部分，不能由谓词正文未使用某变量便擅自删除。

此时 `bst_spec_inhabited n a` 给出每个参数赋值下的目标见证；正尺寸分解
也对所有参数赋值成立。节点构造后，在 `r=precise(n),lo=precise(a)` 的
上下文中，以待证的 `CT_Sub` 实例换回 `q_tree_bst_range r lo ν`。
从变量谓词换到常量谓词、增加或替换支持集的步骤同样须证明，不能当作定义相等。

另一种可行的候选接口是增加纯参数不变量 `I(S)`，要求上下文蕴含
`over(atom I)`，仅在 `I` 下要求非空与分解。它不是程序运行语义的引入规则，
本轮也没有证明它不可行；只是优先研究上述固定常量方案，避免增加此接口。

### 保留最小归纳假设，右递归覆盖任意实际左树

强归纳目标仍为任意下界 `a` 和互异参数名下的三变量上下文判断，环境取 `Σ=∅`：

```text
Δ(n,a;u,v,g) = u:precise(n), v:precise(a), g:range_ty
Δ(n,a;u,v,g) ⊢ app3 G u v g : UTree {ν | B(u,v,ν)}.
```

额外世界变量通过真正的上下文投影证明处理，不在 IH 中假定任意背景上下文稳定。
`CT_CtxSub` 只要求观察变量上的 `ty_env_agree_on` 和限制世界的扩展见证，
不要求完整擦除环境相等（源码 `Typing.v` 的 `ctx_sub_under`）。
同擦除要求属于 `CT_FiberCases` / `CT_CtxCases`。

第二次递归的分类集仍取
`X_R={r,lo,pivot,right_size,root,left_tree}`，索引为
`{(p,tL) | 1≤p≤n}`，其中 `tL` 遍历所有 `tree`，包括 `Leaf` 和不完整树。
每个 case 与原上下文擦除相同，但只保留所需内容：

- `r,lo,pivot,right_size,root,left_tree` 改成该纤维的精确常量。
- `range` 保持原持久类型；须证明子纤维与原世界在 `{range}` 上投影相同，
  再用公式最小性搬运绑定的完整内容，单点的形状本身不够。
- `isz,left_size` 等不再需要的绑定改成同基本类型的 over-top，并从基本世界
  模型证明这些绑定；不能保留原左树的 under 覆盖。

在固定 `(p,tL)` 的 case 中，以 `n-p<n` 使用 IH：

```text
Δ(n-p,a+p;right_size,root,range) ⊢ eR : UTree B(right_size,root,ν)
                       │ CT_CtxSub：实际证明限制世界满足 Δ
Γ(p,tL) ⊢ eR : UTree B(right_size,root,ν)
                       │ CT_Sub：固定参数下替换谓词与支持
Γ(p,tL) ⊢ eR : UTree ΦR(S,pivot,left_tree,ν)
                       │ CT_FiberCases：各 case 使用同一目标
ΓR ⊢ eR : UTree ΦR(S,pivot,left_tree,ν)
```

over 算术图和基本类型给出各纤维的实际常数；精确常量绑定的 under 成分
仍须由单值纤维证明。`ty_denote_gas_over_ret_fvar_fiber_stable_any` 只保持
`CTOver`，不能直接用于 `precise_ty = CTInter over under`。
右树依赖左树的支持是恢复组合覆盖的关键，不能只证明两边各自的边际覆盖。

### 剩余证明依赖与复核边界

建议实施顺序为：

1. 将返回变量的 base denotation 连接到同一原世界的条件覆盖/逐 store over
   满足性；优先复用已有 `ty_denote_gas_under_ret_fvar_self_body_iff`。
   基础 under 的深度为 `1`，使用该引理时取 `gas=0`；任意零 gas 的 guard
   本身不蕴含覆盖。
2. 证明候选节点规则与选择规则的完整 soundness，再提供真实语法推导规则。
   如能由已有构造子派生则给派生证明，否则扩充 `has_context_type`，并在
   `ContextTyping/theories/Soundness.v` 的 `Fundamental` 接入新分支。
   单独的语义 soundness 引理不能当作 `has_context_type` 构造子。
3. 选择规则可先限定左支闭合，足够处理 `ret Leaf`，并带目标 WF 条件。
   右支已有 under 提供非空性；两支 typing 提供 must-termination，结果并集
   提供右支结果包含于选择结果。仍需证明 result-first 扩展与条件覆盖的桥，
   不能由已证的操作语义并集直接宣称 typing soundness。
4. 证明分类上下文覆盖、固定参数下的支持替换、最小 IH 的上下文搬运，
   以及实际正尺寸调用的有限确定性展开；再串起算术、两次递归与节点构造。
5. 外层使用一次针对 `r` 的 `CT_ArrowIntro`，经认证的有限展开后，使用两次
   `CT_Lam` 引入 `lo` 与高阶 `range`。在基础树结果处分类 `(r,lo)`，
   用 IH 与 `CT_Conv` 搬运，最后以空上下文的持久性引入最外层 `□`。

`ty_denote` 在 `cty_depth τ` 处取固定深度，不是对 gas 全称量化。
`relevant_env` 限制类型环境，并出现在 guard 与结果关系中；不是直接先把
整个世界投影后才解释完整公式。上述两点均已据实际定义纠正 Gemini 的误读。
`tapp_tm` 还有 ANF 管理步骤，不能把全部展开无条件称为一步。

Gemini 在最后一轮确认这些修正，并表示未找到新的具体反例。这只是一轮
非正式审查结论，不代表候选规则 soundness、充分性或完整生成器 typing 已证。
当前最需要机器验证的是节点与选择的 denotation 桥，以及纤维上下文覆盖与
支持替换的完整侧条件。

## 条件覆盖桥完成后的复核（2026-10-17）

本次继续以 `gemini-4-argon` 讨论当前工作区的证明状态。以下明确区分已通过
Rocq 的基础与讨论中的候选；没有把模型的认可当作 soundness 证明。

新增并已通过全项目构建的基础是：

- `ContextLogic/FormulaUnderCoverage.v`：固定参数替换与存储满足性的桥，
  `fib_under_atom_covers_store`，以及反向的
  `fib_under_atom_intro_store_coverage`。反向引理显式要求每个出现的参数
  纤维有目标见证，并覆盖所有满足目标 qualifier 的存储投影。
- `Denotation/ConditionalCoverage.v`：`over_ret_var_store_holds`、
  `under_ret_var_covers_value` 和 `under_ret_var_conditional_coverage`，
  将正深度的返回变量指称连接到同一原世界中的条件覆盖。
  另已证明打开后的 typed qualifier 的参数域与局部闭合性。
- `Denotation/TreeCoverage.v`：`node_coverage_from_variable_denotations`，
  将四个返回变量的实际 denotation 连接到目标节点的可达性。
  它仍不是节点的完整 under 指称或语法 typing。

已检查上述核心引理的 `Print Assumptions`：使用既有的证明无关性、外延性和
经典选择等基础，没有新公理或 `Admitted`。完整节点/选择 soundness、正尺寸
推导及最终 `bst_gen_type_judgement` 仍未完成。

### 接下来应证明的一般桥

基础 under 的引入应从三个条件出发：零 gas 的完整 guard、每个参数纤维的
目标非空性、以及所有目标值的条件求值覆盖。非空与覆盖接口须适用于任意
足够新鲜的结果名，不能只给存在量化的某个名字而省略换名证明。

应用 `base_refinement_intro` 后，任取精确结果扩展 `my`。先由旧世界的
投影相等，将原世界覆盖见证提升到 `my` 中的某个存储；再用求值局部性和
`expr_result_formula_at_fiber_witness` 取得所需结果。最后一次取得的见证
只保证在相关环境的自由域上相等，不保证保持完整旧世界域。
这已经足够：目标 qualifier 的参数域包含于相关环境自由域，打开后的完整
支持仅含这些参数与结果名。随后调用已证的
`fib_under_atom_intro_store_coverage`。

对偶的消去桥用于选择：用表达式自身的规范结果扩展，结合 guard 中的总性，
从 under 指称提取原世界上的条件求值覆盖；再由右分支结果包含于选择结果，
调用引入桥重建选择的 under 指称。两分支的 must-termination 都必须证明。

不能把任意选择结果世界直接当作右分支的精确结果世界，也不能默认过滤后
保留完整旧世界投影。例如相关域为空，旧世界包含 `z=0,1`，选择结果世界
仅含 `(z=0,result=0)` 与 `(z=1,result=1)`。结果在相关域上精确覆盖 `{0,1}`，
旧域投影也完整；筛选只返回 `1` 的右分支结果后却丢失 `z=0`。
此例已做有限集合检查，尚非 Rocq 反模型定理。

### 节点规则与归纳接口的边界

节点语法规则只应含四个真实语法前提、目标 WF、新鲜性/支持条件，以及纯
qualifier 条件；程序求值覆盖只出现在 soundness 辅助定理中。目标桥不必是
`Q ↔ Θ`：覆盖需要 `Θ → Q`，另给真正的 `Θ` 非空性即可。纯参数条件应在
域为 `S` 的存储或合适的已定义参数上陈述，不能要求空存储满足非空参数支持。

最小三变量强归纳判断使用项目真实的 `concrete_Φ` 与 `Σ=∅`，不是空的
primitive 签名。最终目标仍是：

```text
Emp ⊢ᶜ [concrete_Φ; ∅] bst_gen_program : bst_gen_ty
```

`CT_FiberCases` 的索引可固定为所有合法 `(p,tL)`，其中 `tL` 遍历所有树。
不要求每个索引在每个世界实际出现；覆盖前提只对实际非空纤维找一个匹配索引。
固定左树后，旧左树 under 一般不能保留，但不是永远失败：零尺寸的 `Leaf`
纤维或唯一合法目标的纤维可以仍满足它。正确证明不得依赖一般稳定性，须在
各 case 中建立精确常量绑定，再证明同一个右树目标的支持替换与分类合并。

最终建议仍是：一般 under 引入/消去桥 → 节点与选择的完整 soundness 和真实
语法规则 → 分类上下文覆盖及支持替换 → 实际闭合生成器的语法强归纳 → 外层
箭头与 `□`。未发现新反例不等于这些步骤已经 sound，也不能把剩余工作称为
单纯将非正式证明转录为代码。

## 通用覆盖桥与构造规则已落地（2026-10-17）

继续实施后，下列步骤已成为通过 Rocq 的定理，而不再只是上述讨论建议：

- `ContextLogic/FormulaUnderCoverage.v` 新增
  `fib_under_atom_inhabited_store`，从每个实际参数纤维提取目标见证。
- `Denotation/BaseCoverage.v` 完成
  `under_denote_intro_store_coverage`、
  `under_denote_canonical_result_world`、
  `under_denote_elim_store_coverage` 和
  `under_denote_of_result_inclusion`。最后一个传递引理显式保留目标 guard，
  不能用结果包含代替 must-termination。
- `Denotation/Choice.v` 完成存储级选择结果并集、两支 must-termination
  与完整 `choose_under_denotation`。证明只要求相关存储项闭合，允许任意
  额外世界变量；借助通用覆盖桥，最终规则无需此前设想的“左支闭合”限制。
- `Denotation/TreeCoverage.v` 新增纯 qualifier 条件记录
  `node_under_graph_spec` 及完整 `node_under_graph_denotation`。记录显式
  包含目标非空、`Θ → Q`、节点分解、根函数图以及右树的左树参数支持。
  记录不含程序求值证书或世界指称前提。
- `ContextTyping/Typing.v` 新增真正的 `CT_ChooseUnder` 与
  `CT_NodeUnderGraph` 构造子，分别要求两个分支、四个返回变量的语法推导。
  `SoundnessChoice.v` 和 `SoundnessTree.v` 完成相应分支证明，并已接入
  `Soundness.v` 的 `Fundamental`。

`Print Assumptions` 已检查两个覆盖方向、两个构造指称定理及更新后的
`Fundamental`，没有新增公理或 `Admitted`，仍使用既有经典逻辑、选择和外延性
基础。`opam exec -- make -j8` 全项目构建通过，包括重新编译 add/sub 的实例与
完整 context typing。核心 denotation、`CT_Fix`、BST 程序与原始规约保持原样。

当前还缺少 BST 具体中间 qualifier 对上述纯条件记录的实例、分类上下文的
模型覆盖、固定参数下的支持替换与上下文搬运、正尺寸调用展开与强归纳推导，
以及最外层箭头/持久封装。`bst_gen_type_judgement` 仍只是目标命题，不能把
构造规则的 soundness 当作生成器的完整语法类型证明。

## 节点规则完成后的实施接口审查（2026-10-17）

与 Gemini 再讨论三轮后，保留尺寸语法强归纳路线，并将剩余工作明确为五项桥，
不能将它们概括为已完成 soundness 后的代码转录：

1. **固定参数下的支持替换子类型。** 在 case 中，把源、目标 qualifier 的全部
   参数支持纳入同一个全世界恒定的有限赋值 `F ↦ σfix`。由覆盖消去/引入桥，
   用 `<[y:=v]> σ` 归一化查询存储，分别证明谓词搬运、目标非空、覆盖与 guard。
   左调用可取 `F={r,lo,pivot,left_size}`；右调用可取
   `F={r,lo,pivot,right_size,root,left_tree}`。新增支持只在当前 case 内恒定时
   处理，不引入一般 under 支持扩张规则。
2. **前缀提取及最小 IH 上下文重组。** 前者利用 `CtxComma` 的同一世界合取，
   取 `r'=m`，证明观察变量上的环境一致，再用 `CT_CtxSub` 搬运旧变量推导。
   后者独立证明：case 模型蕴含两个闭合单点自然数绑定与闭合 range 绑定时，
   可在同一世界组装三变量 IH 上下文。这不是一般依赖绑定的交换律，不能只
   凭擦除环境里存在三个变量得出该模型。
3. **左右递归的纤维上下文覆盖。** 被分类的基础变量取 precise 常量，不需要的
   绑定用同擦除的 over-top。右侧索引包含所有树 `tL`，包括额外 Leaf 和不完整树。
   必须单独证明单值树的 precise 指称，以及持久 range 在非空子纤维中的完整
   模型保持。各 case 推导相同的 `ΦL` 或 `ΦR` 后才由 `CT_FiberCases` 合并。
4. **实际调用的有限展开与反向折叠。** 对正尺寸，证明 `app3 G r lo g` 与
   `choose Leaf (...)` 的结果集合、must-termination 逐存储等价；外层两次
   `CT_Lam` 后，还需函数体与 `app3` 的等价。仅用有限确定性前缀，不依赖尚未
   证明的内部递归总性。由 `CT_Conv` 搬运已有语法推导。
5. **BST 节点证书实例。** 具体中间 qualifiers 须证明支持严格等式、打开后的
   存储解释、根唯一性、目标非空及树分解，组成 `node_under_graph_spec`。
   节点目标 WF 和四个变量的语法 typing 仍是独立前提。

推荐先完成 1、2、5，再集中证明最有风险的 3；4 可独立推进。随后证明：

```text
对 n 强归纳，∀a,u,v,g（互异），
Δ(n,a;u,v,g) ⊢ᶜ[concrete_Φ;∅]
  app3 bst_gen_value u v g : UTree{ν | bst_spec u v ν}

Δ(n,a;u,v,g) = u:precise(n), v:precise(a), g:range_ty
```

正尺寸的两次 IH 分别使用 `pivot-1<n` 与 `n-pivot<n`。右调用内部先恢复
未分类上下文中的统一 `ΦR`，再由外部 `CT_Let` 引入 `right_tree`；此时最终
上下文仍保留原 pivot、left 的完整覆盖，可前缀提取并使用 `CT_NodeUnderGraph`。

最后只对第一个自然数参数用 `CT_ArrowIntro`，确定性展开后两次 `CT_Lam`，
在基础树结果处分类 `(r,lo)` 并调用上述主定理，最后得到空上下文下的持久类型。
这个依赖顺序不要求先有整个生成器的箭头 typing 才能使用较小尺寸 IH。

本轮仅完成讨论与源码复核，没有新增机器证明或执行全项目构建。上述五项桥与
最终强归纳仍待验证；任何正在编写的 qualifier 草稿均不计入已验证结果。

## 上述实施接口的机器证明进展（2026-10-17）

继续实现后，本轮已通过 Rocq 的组件如下。这些是新增的实际定理，不是对讨论
意见的重复确认；最终生成器 typing 仍未完成。

- `Denotation/ResultQualifier.v`：完成 `param_result_qual` 的参数域、局部闭合、
  打开后的精确支持与存储满足性，以及 typed wrapper 的冗余性。
  `QualifierStore.v` 给出 qualifier 的作用域、按支持投影相等的搬运、结果值提取
  与 `<[y:=v]> σ` 查询归一化。
- `Denotation/FixedParameters.v`：`under_denote_fixed_parameters` 完成固定参数
  下改变支持的完整指称传递。它显式要求目标零 gas guard；目标非空性从源 under
  转移，覆盖只保留目标支持。`ContextTyping/FixedParameters.v` 据此证明
  `sub_type_under_pointwise_fixed`，利用源总性重建目标 guard，作为已有 `CT_Sub`
  可用的派生子类型。没有增加原始类型规则。
- `CaseStudy/BSTNodeTypes.v`：定义固定 `n,a` 下的 pivot、root、left、right、
  result 五个中间 qualifier；right 的支持严格含 `left_tree`。完成
  `bst_node_under_graph_spec` 的全部纯条件，包括非空性和树分解；
  `bst_node_context_typed` 从四个真实变量 typing 前提导出节点 typing。
  这尚未证明原始程序的 continuation 满足这些前提。
- `ContextTyping/Weakening.v`：`ctx_sub_comma_prefix` 和 `typing_comma_prefix`
  通过同一世界中的前缀模型完成加性弱化，不假设删除 store 后 under 稳定。
  `CaseStudy/BSTContext.v` 完成闭合 range 类型、最小三变量 `bst_call_ctx` 的
  WF、模型组装和 `CT_CtxSub` 接口，以及闭合末尾绑定的提取。
  `bst_call_ctx_sub` 明确要求实际绑定模型及观察域上的环境一致。
- `ContextTyping/ConstCases.v`：推广自然数常量到全部基础常量，完成
  `const_bind_denote_fiber`。已知基本类型模型、被分类变量的实际常量值时，
  非空纤维满足该常量的完整 precise 绑定，涵盖任意树 `tL`。
- `Denotation/PersistSubset.v`：完成 `ctx_bind_persist_res_subset`。证明先利用
  持久绑定整个相关投影为单点，再由非空同域子世界和公式最小性搬运完整模型；
  没有假定普通递归箭头或任意 under 类型具有子世界稳定性。
  `BSTContext.bst_range_binding_fiber` 已将它用于真实 `range_ty`。
- `CaseStudy/BSTSupport.v`：证明原始自由参数 BST qualifier 与显式支持构造的
  等价及其打开后存储解释，保留原始规约，供上述子类型桥实例化。
- `BSTGeneratorUnfolding.v`：新增实际函数的部分应用与打开体视图，证明
  `bst_call_body_prefix` 和 `bst_positive_call_prefix`。对固定自然数尺寸、下界及
  任意具备基本函数类型的 range 值，有限确定性展开停在原函数体或正尺寸选择
  分支入口，保留内部递归调用。结果集合与 must-termination 等价可由既有
  `arithmetic_prefix_equivalence` 取得，不预设内部递归总性。

全项目 `opam exec -- make -j8` 通过。对上述主要接口执行 `Print Assumptions`，
没有新增公理或 `Admitted`，仍使用项目既有经典逻辑、外延性、证明无关性与选择。

下一步仍须将支持桥和上下文接口实例化到左右实际递归调用，组装完整分类上下文
覆盖；还需变量实参与固定自然数展开之间的替换、外层函数体折叠接口、尺寸强归纳
与最终箭头/持久封装。尤其不能把 `bst_node_context_typed` 的四个假设当作已经
为原始程序证明。`bst_gen_type_judgement` 目前仍只是目标命题。

## 固定支持桥完成后的四轮实施审查（2026-10-17）

本轮取得四轮有效答复，临时记录为 `request/response-bst-14` 至 `bst-17`。
审查包含已编译的 `sub_type_under_worldwise_fixed`、原规约存储解释、最小
上下文的查找性质，以及已有节点证书、持久绑定和常量纤维接口。
讨论中的新增接口仍未成为 Rocq 定理；本轮没有修改程序、核心语义或类型规则。

### 主判断与上下文链

继续对实际闭合值 `G = bst_gen_value` 的尺寸作语法强归纳：

```text
∀ n a u v g（名字互异），
  Δ(n,a;u,v,g) ⊢ᶜ[concrete_Φ;∅]
    app3 G u v g : Under Tree (q_tree_bst_range u v ν)

Δ(n,a;u,v,g) = u:precise(n), v:precise(a), g:range_ty
```

世界仍可包含任意额外变量。归纳假设是实际调用的语法推导，不是假设任意
`self` 的混合世界契约，也不从运行正确性直接产生 `has_context_type`。

固定 `n>0,a`，令 `S={u,v}`，从 `Γ0=Δ(n,a;u,v,g)` 按原程序次序追加：

| 新绑定 | 计划使用的类型 | 参数支持 |
| --- | --- | --- |
| `pivot` | `precise_ty TNat (bst_pivot_qual S n)` | `S` |
| `left_size` | 原 `op_minus1` 结果类型的 Over 分量 | `{pivot}` |
| `right_size` | 原 sub 的 `q_nat_graph` 结果类型的 Over 分量 | `{u,pivot}` |
| `root` | `CTOver TNat (bst_root_qual S pivot a)` | `S∪{pivot}` |
| `left_tree` | `CTUnder TTree (bst_left_qual S pivot n a)` | `S∪{pivot}` |
| `right_tree` | `CTUnder TTree (bst_right_qual S pivot left_tree n a)` | `S∪{pivot,left_tree}` |

`pivot` 的 Over 分量保证每个实际存储都有 `1≤pivot≤n`，Under 分量供最终
节点覆盖使用；只保留 Under 会允许非法额外 pivot，无法据此证明递减。
三个算术中间值只需 Over 等式图，不必保留其 Under 分量；`left_size`、
`right_size` 无需额外补齐 `S` 支持。对应的算术应用包装仍须写出实际推导。

六层 `CT_Let` 延续的共同结果为 `Under Tree (bst_result_qual S n a)`，其自由
参数只有 `S`，因此局部 pivot、尺寸、根和树变量均不逃逸到外层结果类型。

### 左右分类的精确边界

左分类取 `X_L={u,v,pivot,left_size}`，索引只需合法 pivot：
`I_L={p:nat | 1≤p≤n}`。在 case 内把 `pivot,left_size` 绑定为 `p,p-1` 的
precise 常量，`right_size,root` 改为同擦除的 Over-top，保留原位置的
`g:range_ty` 及固定 `u,v`。

右分类取 `X_R={u,v,pivot,right_size,root,left_tree}`，索引为 `I_L×tree`。
case 内把相关绑定精确化为 `p,n-p,a+p,tL`，`left_size` 改为 Over-top。
`tL` 遍历所有树，包括 `Leaf` 与不完整树，不附加 `bst_spec` 条件，也不保留
原左树 Under 绑定。各 case 与相应原上下文保持绑定次序及完整擦除环境一致。

合法索引使每个 case 都有 `p-1<n`、`n-p<n`。不能先定义可满足的无约束
数值 tuple case，再只证明其中“实际出现”的那些 case；`CT_FiberCases`
要求对所有索引都有语法推导。使用上述索引是一种简单方案，并非唯一编码。

纤维模型覆盖的待证组合链为：在原上下文模型中取非空纤维的代表存储；由
前缀提取和右绑定的实际环境取得返回变量指称；对 pivot 取 `CTInter` 的 Over
分量，再用 `over_ret_var_store_holds` 读出合法区间及三个算术等式。
同一 pivot 的一致性依靠查找值单射，不依靠非确定生成器的求值确定性。
继而用 `const_bind_denote_fiber`、持久 range 的子世界搬运、Over-top 的基本
世界证明及闭合绑定拼接，组装 case 模型。不能跳过实际环境或凭基本类型查找
推出整个依赖绑定模型。

两个分类集分别包含于对应调用项和共同目标类型的相关自由域：左侧还含 `g`，
右侧还含 `g`。左集合不加入 `root/right_size`，右集合不加入 `left_size`。
右 qualifier 的显式 `left_tree` 支持，使右树覆盖在每个左树纤维中成立，
排除仅有边际覆盖、缺少左右交叉组合的世界。

IH 给出的源类型直接是自由参数版 `q_tree_bst_range left_size lo ν` 或
`q_tree_bst_range right_size root ν`。在 case 内分别取共同固定支持
`F=X_L` 或 `F=X_R`，用 `sub_type_under_worldwise_fixed` 转为同一个
`bst_left_qual` 或 `bst_right_qual`，随后才用 `CT_FiberCases` 合并。
不能反向使用只证明“常量版→自由参数版”的 `q_bst_constants_subtype`。

最终节点处保持未分类的完整上下文。右树直接用 `CT_VarR`；左树、根和 pivot
先在各自前缀用 `CT_VarR`，再用已证 `typing_comma_prefix` 搬运，pivot 另取
Under 分量。这四个真正的变量推导才能接入 `bst_node_context_typed`。

### `range 1 r` 与仍待证明的 Over 桥

应用规则的实参必须是变量。计划先推导辅助项：

```text
let one = ret 1 in app2 g one u
```

在其内部通过已有持久变量消除、两次应用及子类型，得到不依赖 `one` 的
pivot precise 目标，然后用 `CT_Conv` 消去这一步确定性 let，恢复原始
`app2 g 1 u`。两项的结果集合和 must-termination 等价均须证明；程序不改写。
源 precise 结果的 Over、Under 分量分别转换后合并，不能把 Under 桥直接用于
整个 `CTInter`。Under 转换的固定集可取 `{one,u,v}`，这些变量在此确实恒定。

另一个缺口是 root 的 Over 转换：原 add 图为 `ν=v+p`，目标为 `ν=a+p` 且
支持为 `S∪{p}`。上下文保证 `v=a`，但未分类的 `p` 可以取多个值，因此不能
调用要求全部参数恒定的 Under 桥。拟证明一般 Over 后果子类型，候选前提为：

```text
wf Γ，Over b φ1 与 Over b φ2 在 erase Γ 下良构；
∀ m y σ w，m ⊨ ctx Γ → σ∈m →
  y∉world_dom(m)∪qual_dom φ1∪qual_dom φ2 →
  holds(open y (typed φ1), <[y:=w]>σ) →
  holds(open y (typed φ2), <[y:=w]>σ)
─────────────────────────────────────────────────
Γ ⊢ Over b φ1 ≤ Over b φ2
```

这只是待证接口。需要正深度 Over 指称与原世界存储上所有可达结果满足谓词的
消去/引入桥，利用源总性和目标静态良构重建 guard，并显式处理相关支持变化、
查询归一化及结果扩展。不能假设语义结果见证保持完整旧存储；更不能把该语义
辅助引理直接当作新的语法 typing 入口。它只为已有真实推导提供 `CT_Sub`。

Gemini 给出的候选代码曾有自反占位等式，并反复把“限制类型环境”误述为
“先投影完整世界”。这些代码与证明表述均未采用，第四轮已明确撤回。
从 `CtxComma` 取右支模型后，才可在其实际环境上应用
`ctx_denote_under_bind_inv`；不能一步声称得到完整前缀擦除环境下的指称。

### 合龙顺序与验证状态

节点、六层 let、选择与有限展开先产生共同的 `bst_result_qual S n a`。
在 `Γ0` 中，`u=n,v=a` 全世界恒定，直接以固定支持 `F=S` 转回原始
`q_tree_bst_range u v ν`。常量版 qualifier 支持为空，不能仅凭数学谓词相同
就把它与支持为 `S` 的 `bst_result_qual` 当作相等。

顶层仍采用：一次 `CT_ArrowIntro` 引入 `r` →有限展开→两次 `CT_Lam` 引入
`lo,range` →仅在基础 UnderTree 目标处分类 `(r,lo)` 并接入主判断→最外层
`CT_PersistIntro`。不在箭头结果处使用基础 Under 的 joinability，也不需
再次穿过已由 `bst_positive_call_prefix` 消去的 `isz/match`。

建议依次完成 Over 后果桥与 range/算术应用包装、变量实参的零尺寸基础、左右
case 的固定支持转换及模型覆盖、正尺寸尺寸强归纳、顶层封装。
本轮 `opam exec -- make -j8` 通过，但没有新增 Rocq 定理；上述待证项和
`bst_gen_type_judgement` 均未完成。Gemini 最后一轮表示未找到具体反例，
这不能替代这些义务的机器证明。

## 四轮讨论后的机器验证进展（2026-10-17）

上述讨论结束后，已实际补齐并编译以下接口：

- `Denotation/OverConsequence.v`：正深度 Over 指称与原世界实际存储中
  所有可达结果满足打开后的谓词之间的消去、引入和后果桥。结果世界的查询
  归一化只搬运相关支持上的查找，不要求语义结果见证保持完整旧存储。
- `ContextTyping/OverConsequence.v`：`sub_type_over_store_consequence`
  和 `sub_type_under_inter_intro`。它们只为已有语法推导提供 `CT_Sub`，
  没有新增 `has_context_type` 构造子。
- `BSTArithmeticSupport.v`：`q_nat_graph_free_param` 与
  `bst_root_arithmetic_subtype`。上下文固定下界变量为 `a` 时，原 add 的
  Over 图 `ν=lo+p` 可转换为支持 `S∪{p}` 的节点根类型；不要求 `p`
  全世界恒定。这只是子类型转换，实际 add 应用的上下文包装仍待完成。
- `BSTGeneratorTyping.v`：变量实参的语义等价转换，以及
  `bst_zero_call_minimal_context_typed`，即主归纳所需的真实零尺寸基础：
  在 `Δ(0,a;u,v,g)` 中，对原始 `G u v g` 推导原始自由参数 BST 结果类型。
  不是把主归纳判断作为假设，也没有改写原程序。

这些文件已包含在 `_CoqProject` 中，完整 `opam exec -- make -j8` 与
`git diff --check` 均通过。主要接口的 `Print Assumptions` 只列出项目既有
经典逻辑、选择、外延性与证明无关性，没有新增公理或证明占位。
正尺寸 case 的模型覆盖、range/算术应用包装、
主强归纳与顶层封装仍待完成，`bst_gen_type_judgement` 仍只是目标命题。

## 算术应用与左递归分类的机器证明（2026-10-17）

以下新增接口均已编译通过，继续使用原始程序、规约和既有 typing 构造子。

- `ContextTyping/BasicBindings.v`：从上下文基本模型提取单变量的基本世界模型
  和闭合值类型；从基本模型重建闭合 Over-top 绑定，并通过现有 `CT_Var`
  与 `CT_CtxSub` 推导 `typing_over_top_var`。另提供闭合绑定追加的良构性
  与擦除环境查找接口。它不重建任意依赖 refinement 或普通箭头绑定。
- `NatArithmeticApplications.v`：`arithmetic_app2_context_typed` 对任意良构
  依赖上下文中的两个不同自然数变量，推导原始 add/sub 双参数应用的 precise
  算术图。先在同一世界重建两个 Over-top 输入绑定，搬运已有算术体的真实
  推导，再用已认证的有限展开及结果/must 等价恢复实际应用。
  `arithmetic_app2_over_context_typed` 取其 Over 分量。
- `BSTArithmeticSupport.v`：`bst_root_arithmetic_context_typed` 已将实际
  `add lo pivot` 接到 `bst_root_qual`，不要求 pivot 在整个世界恒定。
- `BSTRecursiveSupport.v`：`bst_left_fixed_call_subtype` 与
  `bst_right_fixed_call_subtype` 将原始自由参数 BST 类型转为共同的左右条件
  类型。前提明确要求分类支持在当前世界恒定、尺寸和下界具有指定值、pivot
  合法及支持在作用域中。右侧固定支持保留左树变量，未声称一般支持扩张成立。
- `ContextTyping/FiberSupport.v`：基础 Under 的 joinability 可由静态良构性
  及分类集包含于项/类型的观察支持推导。该引理不适用于任意箭头或含 `□` 的
  结果类型。
- `BSTRecursiveCases.v`：定义实际顺序的左 case 上下文：最小 `Δ(n,a)` 后
  依次为 `pivot:precise(p)`、`left_size:precise(p-1)`、
  `right_size:Over-top`、`root:Over-top`。证明其良构、查找、完整绑定提取及
  在 `{u,v,pivot,left_size}` 上恒定。`bst_left_case_recursive_typed` 将
  较小尺寸真实调用的推导搬入该 case，并接到共同左树类型。

左 case 的模型覆盖也已完成：`bst_left_case_fiber_model` 用代表存储的实际
查找构造 precise 常量绑定，用完整持久 range 绑定的纤维保持搬运 range，
用基本世界模型重建两个无关 Over-top 绑定，再逐层组装完整 case 模型。
`bst_left_case_fiber_cover` 从原上下文的固定参数、合法 pivot 和尺寸等式取得
合法索引。没有从基本类型查找直接推断任意依赖绑定，也没有假设左右独立。

`bst_left_recursive_context_typed` 将上述 case 的语法推导、模型覆盖和
joinability 接入既有 `CT_FiberCases`。递归前提只要求合法 `p` 下的实际
`G (p-1) lo range` 推导，显式检查 `p-1<n`。原上下文仍作为参数：必须有
正确的擦除环境、完整 range 绑定，以及每个实际存储上的参数和尺寸等式。
这些前提还没有在原始正尺寸 BST 的具体四层 let 延续中全部实例化。

完整 `opam exec -- make -j8` 与 `git diff --check` 通过。主要新接口的
`Print Assumptions` 未显示新增公理或证明占位。尚待完成右 case 的具体上下文
及模型覆盖、range 应用包装、正尺寸实际上下文的事实提取和两侧实例化、节点与
六层 let 组装、主尺寸强归纳和顶层封装。最终判断仍未证明。

## 右递归与实际正分支上下文的机器证明（2026-10-17）

本节记录三轮续谈后的本地验证，不把 Gemini 的候选代码作为已证结论。

- `BSTRightRecursiveCases.v` 已补齐右 case 的良构、擦除查找、完整绑定
  提取、固定支持、纤维模型和覆盖。索引为合法 `p` 与任意实际左树 `t`；
  不保留原左树的 Under 覆盖，也不要求 `t` 是合法完整 BST。
  `bst_right_recursive_context_typed` 用较小尺寸的真实调用推导，得到带左树
  支持的共同右树类型，再接入现有 `CT_FiberCases`。
- `BSTArithmeticSupport.v` 新增 `bst_pred_primitive_context_typed`：原程序的
  `op_minus1 pivot` 由 `CT_AppOp` 与 Over 后果子类型得到支持 `{pivot}` 的
  `ν=pivot-1` 图。`QualifierStore.v` 的结果 qualifier 打开与存储求值消去桥
  为该证明提供接口，没有直接从运行语义生成任意 typing。
- `BSTPositiveContext.v` 按原始程序顺序定义 pivot、left size、right size、
  root、left tree、right tree 的实际依赖上下文并证明良构。从 `CtxComma`
  右绑定的实际限制/扩充环境读取 Over 或 precise 的 Over 分量，逐层取得
  同一实际 store 中的合法 `p`、`p-1`、`n-p`、`a+p`；没有把依赖绑定提到
  空环境，也没有声称所有实际左树满足 BST 规约。
- `bst_left_call_positive_context_typed` 与
  `bst_right_call_positive_context_typed` 已在这些实际上下文中实例化左右
  分类接口。其递归前提只要求相应严格较小尺寸的真实最小上下文调用 typing，
  供尚未完成的主强归纳使用。
- `bst_positive_node_context_typed` 已由四个真实变量推导接入节点规则：
  pivot 用 precise 的 Under 分量，root 用 Over，左右树用各自的 Under。
  依赖变量由 `CT_VarR` 和前缀弱化取得；没有仅凭纯节点证书生成 typing。
  通用静态包装 `typing_var_right_wf`、`typing_comma_prefix_wf` 只使用既有
  构造子，没有新增规则。

上述文件全部已注册到 `_CoqProject`，完整 `opam exec -- make -j8` 与
`git diff --check` 通过。11 个主要新接口的 `Print Assumptions` 仅列出项目既有
经典逻辑、选择、外延性和证明无关性，没有新增公理或证明占位。
尚待完成 `range 1 r` 的局部代理与两次依赖应用、
六层 let 和选择/有限展开的组装、主尺寸强归纳、顶层箭头与 `□`。
`bst_gen_type_judgement` 仍只是目标命题，尚无最终证明。

## 原始 range 调用的机器证明（2026-10-17）

`BSTRangeTyping.v` 已完成 `bst_range_call_context_typed`：在最小上下文
`Δ(n,a;u,v,g)` 中，`n>0` 时，原始项 `app2 g 1 u` 具有
`precise_ty TNat (bst_pivot_qual {[u;v]} n)`。它没有改变 range 或生成器程序。

该文件逐层证明了 qualifier 打开与合取的兼容性、两次依赖箭头打开的精确
索引、区间 qualifier 的存储解释，以及以下真实语法推导：

- 在局部 `one:precise(1)` 上下文中，先消除持久 range 得到普通箭头，再用
  `CT_AppFun` 得到含 `one` 的中间函数；第二次应用前证明 `ret u` 满足
  `one≤ν` 的 Over 实参类型，并显式核对两次应用的新鲜性。
- 通过 `CT_Let` 绑定中间函数，得到原始区间 precise 结果。其到 pivot
  precise 类型的转换，以同一个源类型分别经交集投影、Over 后果桥、固定
  支持的 Under 桥及 `sub_type_under_inter_intro` 合并；不使用不存在的
  交集引入构造子。Under 桥固定 `{u,v,one}`，不假设一般支持扩张成立。
- 在消去 `one` 以前，结果类型已不含 `one`。外层 `CT_Let` 得到局部代理项，
  `bst_range_proxy_prefix` 证明其确定性一步前缀与原调用的结果及
  must-termination 等价，随后由既有 `CT_Conv` 恢复原始 `app2 g 1 u`。

该模块已注册 `_CoqProject`，完整 `opam exec -- make -j8` 与
`git diff --check` 通过。7 个关键接口的 `Print Assumptions` 只显示项目既有
经典逻辑、选择、外延性与证明无关性，没有新增公理或证明占位。
最终 `bst_gen_type_judgement` 仍未证明；当前主要剩余项为六层 let 与选择的
正分支组装、变量/常量版本的有限展开转换、主尺寸强归纳以及顶层箭头与 `□`。

## range 完成后的组装审查（2026-10-17）

三轮 Gemini 续谈与本地独立复核后，仍优先用现有规则完成实际 `bst_gen_value`
的推导，不修改程序、规约、指称或 `CT_Fix`，暂不增加递归规则。
这是实施建议，不是最终可导性的保证。讨论纠错见 `GeminiDiscussion.md`
“range 调用完成后的三轮组装审查”。

最新代码中，`BSTPositiveTyping.v` 已定义原始六层 let 的阶段，证明
`bst_positive_branch_generate` 及各阶段的 STLC typing。实际自由变量实例的
let 打开可按定义通过 `change` 匹配；不必先补六个命名打开引理。
这些基本类型证明尚未构成任何阶段的 context typing。

接下来按以下五项里程碑验证：

1. **六层 let**：先在 `Γ5` 用右递归接口和节点接口证明 right stage，向外
   依次接 left、root、sub、pred、range。共同结果始终为
   `Under Tree (bst_result_qual {[u;v]} n a)`。算术接口直接实例化实际上下文，
   提供 WF、擦除查找与存储事实；两次递归的前提来自严格较小尺寸的真实调用。
2. **正分支收尾**：`CT_ChooseUnder` 的 Leaf 分支仅取 Over-top。六层 let
   提供 Node 分支的精确目标覆盖。在 `Γ0` 用
   `sub_type_under_worldwise_fixed`（`F={u,v}`）将共同结果转回原自由参数
   qualifier；支持非空的 `bst_result_qual` 不能当作空支持的常量 qualifier。
   另证变量正分支实例化与已有常量有限前缀衔接，由 `CT_Conv` 恢复实际调用；
   结果等价和 must-termination 等价均须逐存储验证。
3. **主强归纳**：对 `n` 强归纳，命题内部全称量化 `a,u,v,g`，从而可以对
   `(p-1,a;ls,v,g)` 与 `(n-p,a+p;rs,k,g)` 应用 IH。结合已证零尺寸基础，
   得到所有尺寸在最小上下文中的原始调用 typing。模型仍允许任意额外坐标；
   不能误将最小类型环境解释成只含三个变量的世界。
4. **顶层参数引入**：一次 `CT_ArrowIntro` 引入 `r`，以 `CT_Conv` 连接
   单参应用与 `ret (bst_partial r)`，再两次 `CT_Lam` 引入 `lo,range`。
   partial 的行政前缀不执行 `op_eq0`，转换逐存储检查，不要求混合世界中
   所有 `r` 有共同上界。HAT 的 `HS_Fix` 打开尺寸实参，后续 beta 绑定
   self。类型打开须按真实 `arg2=#3,arg1=#2,ν=#0` 核验，结果 qualifier
   三次打开深度为 `3,2,1`，最后一次不改变结果。
5. **基础 Under 分类与最终封装**：在完整三参数上下文、原始函数体目标处，
   对 `{r,lo}` 使用 `CT_FiberCases`。从原完整世界提取 pair 前缀模型，
   用 `nat_pair_fiber_constants` 获得 `(n,a)`；另提取完整闭合 range
   绑定，经 `bst_range_binding_fiber` 保持，再组装 `bst_call_ctx`。
   不先投影成 pair 世界，也不从基本函数查找重建 range 契约。各 case 中
   通过 `bst_call_body_prefix` 及变量实例化的 `CT_Conv`，从主调用推导得到
   原始函数体推导。只在基础 Under 使用 joinability，最后在 Emp 用
   `CT_PersistIntro` 完成目标。

当前完整 `opam exec -- make -j8` 通过；本轮只更新讨论与计划，没有完成上述
五项或增加新规则。最终 `bst_gen_type_judgement` 仍是待证命题。后续只有相应
推导脚本编译通过并检查其假设后，才能把这些候选步骤记为已证。

## 完整 typing 的机器证明（2026-10-17）

上述五项里程碑现已全部完成，并证明原始闭合生成器的完整目标：

```coq
Theorem bst_gen_type_judgement_holds : bst_gen_type_judgement.
```

证明在 `theories/BSTGeneratorContextTyping.v`，其主体
`bst_gen_context_typed` 的类型为
`has_context_type concrete_Φ ∅ CtxEmpty bst_gen_program bst_gen_ty`，
无未完成的递归或覆盖前提。`bst_gen_denotational_sound` 直接应用已有
`concrete_Fundamental`，得到该完整判断的指称 soundness。

本轮实现对应关系如下：

| 里程碑 | 已编译的主要接口 |
| --- | --- |
| 原始六层 let | `BSTPositiveTyping.bst_generate_stage_context_typed` |
| 结果转换、选择与变量级正分支展开 | `BSTSupport.bst_result_to_free_subtype`、`BSTPositiveTyping.bst_positive_branch_context_typed`、`BSTCallTyping.bst_positive_call_minimal_context_typed` |
| 任意尺寸的真实调用强归纳 | `BSTCallTyping.bst_call_minimal_context_typed` |
| partial 展开、参数类型打开和两层 lambda | `BSTGeneratorUnfolding.bst_partial_prefix`、`BSTGeneratorContextTyping.bst_generator_first_open` / `second_open` / `third_open`、`bst_partial_context_typed` |
| 基础 Under 分类和完整持久封装 | `BSTGeneratorContextTyping.bst_top_ctx_fiber_cover`、`bst_open_body_top_context_typed`、`bst_gen_context_typed` |

六层 let 的真实推导从节点向外组装；递归前提只使用严格较小尺寸的实际闭合
`bst_gen_value` 调用。主归纳对所有下界与参数名统一量化，随后解除该前提。
正分支结果在相同 `{u,v}` 支持上转回原始自由参数 qualifier；选择的额外 Leaf
只需 Over-top。所有转换同时证明结果集合和 must-termination 等价。

顶层按原计划先引入全部参数，才对基础 Under 分类。模型覆盖直接使用原世界的
pair 前缀模型及完整持久 range 绑定的同域纤维保持，不把世界投影当作独立性，
不从基本查找重建 range 契约，也不假设普通箭头或任意含 `□` 结果可拼接。
最终由一次 `CT_ArrowIntro`、两次 `CT_Lam` 和 `CT_PersistIntro` 封装。

验证证据：

- 完整 `opam exec -- make -j8` 通过，所有新模块已注册 `_CoqProject`。
- 独立 `rocq check -silent` 对 `CaseStudy.BSTGeneratorContextTyping` 及其
  递归依赖检查通过，未使用 `-admit` 或 `-norec`。临时日志为
  `/private/tmp/bst-completed-typing-kernel-check.log`。
- 10 个主要接口（含最终 typing、soundness 和 add/sub）的
  `Print Assumptions` 检查通过；假设只有项目既有的经典排中律、经典不定描述、
  函数外延性、命题外延性及证明无关性。临时审计源码和日志分别为
  `/private/tmp/CheckBSTCompletedTyping.v` 与
  `/private/tmp/bst-completed-typing-assumptions.log`。
- 原始 `bst_gen`、`bst_gen_ty`、类型指称和 `CT_Fix` 未修改。本轮只组合已证
  规则并补充所需引理，没有新增类型规则、公理或 `Admitted`。

早期章节中的“尚未证明”描述均对应当时的阶段；不再表示当前最终判断的状态。
