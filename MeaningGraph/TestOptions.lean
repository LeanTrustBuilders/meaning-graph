import MeaningGraph

/-!
# The dependency lists, the rule, and closures

Checked on Lean core, analysed as a project (`Init.Data.List`) sitting on the rest of core. Not a
`module`: a module imports others at their exported level, where definitions come without their
values, and the walks would see no bodies.

Run with `lake build MeaningGraphTest`.
-/

open Lean MeaningGraph MeaningGraph.Hash

namespace MeaningGraph.TestOptions

-- Which constants are declarations: projections and constructors are, for completion's rule, and
-- not for the suite's; a recursor is for neither.
/-- info: [(false, true), (false, true), (false, false), (true, true)] -/
#guard_msgs in
#eval show MetaM (List (Bool × Bool)) from do
  let env ← getEnv
  let suite := Context.of env `Init.Data.List
  let completion := Context.of env `Init.Data.List { rule := .completion }
  return [``Prod.fst, ``Prod.mk, ``Nat.rec, ``Nat.gcd].map fun n =>
    (suite.isNode n, completion.isNode n)

/-- Whether every dependency of `names` is a declaration under the context's rule. -/
def onlyNodes (ctx : Context) (names : Array Name) : MetaM Bool := do
  let (deps, ctx) ← ctx.depsOf names
  return deps.all fun (_, d) => (d.statement ++ d.meaning ++ d.term).all ctx.isNode

-- Helpers are looked through wherever they come from: `Nat.gcd` is defined by well-founded
-- recursion, through helpers; `List.foldl` by structural recursion, through `List.rec`; `Prod.fst`
-- is a projection.
/-- info: (true, true) -/
#guard_msgs in
#eval show MetaM (Bool × Bool) from do
  let env ← getEnv
  let upstream := #[``Nat.gcd, ``List.foldl, ``Nat.lt_irrefl, ``Prod.fst]
  return (← onlyNodes (Context.of env `Init.Data.List) upstream,
    ← onlyNodes (Context.of env `Init.Data.List { rule := .completion }) upstream)

-- Each declaration's lists nest: its statement is part of what it means, and what it means part of
-- what the kernel checked of it. A proof means its statement. On every declaration of the project.
/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  let env ← getEnv
  let ctx := Context.of env `Init.Data.List
  let (deps, _) ← ctx.allDeclDeps
  let mut ok := decide (deps.size > 1000)
  for (n, d) in deps do
    let some info := env.find? n | continue
    ok := ok && d.statement.all d.meaning.contains && d.meaning.all d.term.contains
    if ← isProofDecl info then ok := ok && d.meaning == d.statement
  return ok

/-- The names `Context.closure` reaches from `roots` along `follow`. -/
def reach (ctx : Context) (roots : Array Name) (follow : Follow) : MetaM (Std.HashSet Name) := do
  let (reached, _) ← ctx.closure roots follow
  return reached.foldl (·.insert ·.name) {}

-- The closures nest, statement in meaning in term. A proof is not walked: from a theorem, the walk
-- reaches what its statement does. And under the project boundary the walk does not leave the
-- project: what it reaches upstream, it does not walk into.
/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval show MetaM (List Bool) from do
  let env ← getEnv
  let ctx := Context.of env `Init.Data.List { boundary := .none }
  let roots := #[``List.length_append, ``List.mergeSort]
  let s ← reach ctx roots .statement
  let m ← reach ctx roots .meaning
  let t ← reach ctx roots .term
  let thm := ``List.length_append
  let fromThm ← reach ctx #[thm] .term
  let (thmDeps, _) ← ctx.depsOf #[thm] (term := false)
  let fromStatement ← reach ctx thmDeps[0]!.2.statement .term
  let projectCtx := Context.of env `Init.Data.List
  let (inProject, _) ← projectCtx.closure roots .term
  return [s.toList.all m.contains, m.toList.all t.contains, s.size < m.size, m.size < t.size,
    fromThm.erase thm |>.toList.all fromStatement.contains,
    inProject.all fun r => projectCtx.declModule.contains r.name || r.deps.term.isEmpty]

end MeaningGraph.TestOptions
