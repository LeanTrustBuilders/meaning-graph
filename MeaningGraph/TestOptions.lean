import MeaningGraph

/-!
# The options: where the analysis stops, and which constants are declarations

Checked on Lean core, analysed as a project (`Init.Data.List`) sitting on the rest of core, as
`MeaningGraph.TestEquivalence` does, and for the same reason not a `module`.

Run with `lake build MeaningGraphTest`.
-/

open Lean MeaningGraph

namespace MeaningGraph.TestOptions

/-- Whether, under the default options, looking through helpers is what it was before there were
options (`expandThroughInternals`), on every declaration of the project `root`. -/
def defaultIsProjectBoundary (root : Name) : MetaM Bool := do
  let env ← getEnv
  let ctx := Context.of env root
  let targets := ctx.constants.filterMap fun (name, _, info) =>
    if ctx.exposed.contains name then some (name, info) else none
  return targets.size > 1000 && targets.all fun (name, info) =>
    let used := usedConstantsOf env name info true
    (expandThrough env (!ctx.stopsAt ·) {} used).1 ==
      (expandThroughInternals env root ctx.exposed {} used).1

/-- info: true -/
#guard_msgs in
#eval defaultIsProjectBoundary `Init.Data.List

/-- Whether every dependency reported for `names` is a declaration a person wrote. Under
`Boundary.none` that holds of upstream declarations too; under `Boundary.project` an upstream
declaration's helpers are left as they are. -/
def onlyAuthored (ctx : Context) (names : Array Name) : Bool :=
  names.all fun n =>
    match ctx.env.find? n with
    | none => false
    | some info =>
      let (d, _) := ctx.declDeps {} n info
      (d.typeDeps ++ d.deps).all fun m => (ctx.env.find? m).any (isAuthored ctx.env m ·)

/-- info: (true, false) -/
#guard_msgs in
#eval show MetaM (Bool × Bool) from do
  let env ← getEnv
  let none := Context.of env `Init.Data.List { boundary := .none }
  let project := Context.of env `Init.Data.List
  -- `Nat.gcd` is defined by well-founded recursion, through helpers; `List.foldl` by structural
  -- recursion, through `List.rec`; `Prod.fst` is a projection.
  let upstream := #[``Nat.gcd, ``List.foldl, ``Nat.lt_irrefl, ``Prod.fst]
  return (onlyAuthored none upstream, onlyAuthored project upstream)

-- What is a declaration: projections and constructors are, for completion's rule, and not for the
-- authored rule; a recursor is for neither.
/-- info: [(false, true), (false, true), (false, false), (true, true)] -/
#guard_msgs in
#eval show MetaM (List (Bool × Bool)) from do
  let env ← getEnv
  let authored := Context.of env `Init.Data.List { boundary := .none }
  let completion := Context.of env `Init.Data.List { boundary := .none, display := .completion }
  return [``Prod.fst, ``Prod.mk, ``Nat.rec, ``Nat.gcd].map fun n =>
    (authored.stopsAt n, completion.stopsAt n)

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
  let ctx ← (Context.of env `Init.Data.List { boundary := .none }).withDataValueConsts
  let roots := #[``List.length_append, ``List.mergeSort]
  let s ← reach ctx roots .statement
  let m ← reach ctx roots .meaning
  let t ← reach ctx roots .term
  let thm := ``List.length_append
  let some info := env.find? thm | return []
  let fromThm ← reach ctx #[thm] .term
  let fromStatement ← reach ctx (ctx.declDeps {} thm info).1.typeDeps .term
  let projectCtx ← (Context.of env `Init.Data.List).withDataValueConsts
  let (inProject, _) ← projectCtx.closure roots .term
  return [s.toList.all m.contains, m.toList.all t.contains, s.size < m.size, m.size < t.size,
    fromThm.erase thm |>.toList.all fromStatement.contains,
    inProject.all fun r => projectCtx.declModule.contains r.name || r.deps.deps.isEmpty]

-- `sources` explains every dependency `declDeps` reports, and none it does not: on one declaration in
-- five of `Init.Data.List`, for `dataDeps` and for `deps`, against its dependencies and against a
-- few constants that are not dependencies.
/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  let env ← getEnv
  let ctx ← (Context.of env `Init.Data.List).withDataValueConsts
  let targets := ctx.constants.filterMap fun (name, _, info) =>
    if ctx.exposed.contains name then some (name, info) else none
  let mut ok := decide (targets.size > 1000)
  for h : i in [0:targets.size] do
    if i % 5 != 0 then continue
    let (name, info) := targets[i]
    let (d, _) := ctx.declDeps {} name info
    for t in d.dataDeps do
      if (ctx.sources name info t true).isEmpty then ok := false
    for t in d.deps do
      if (ctx.sources name info t false).isEmpty then ok := false
    for t in [``Nat.gcd, ``Classical.choice, ``List.lookup] do
      if !d.deps.contains t && !(ctx.sources name info t false).isEmpty then ok := false
  return ok

end MeaningGraph.TestOptions
