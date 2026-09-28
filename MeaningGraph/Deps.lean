module

public import MeaningGraph.Hash

@[expose] public section

/-!
# What each declaration of a project rests on

Three lists per declaration (`DeclDeps`), each the edges of one of the walks of `MeaningGraph.Hash`,
so that every hash follows its graph by construction:

* `statement`: what its type mentions, proofs erased;
* `meaning`: what it means, proofs erased everywhere: its statement for a proof, its statement and
  value for a definition, its types and constructors for an inductive type. The meaning hash follows
  this graph;
* `term`: everything the kernel checked of it, proofs included. The content hash follows this graph.

Each looks through the constants that are not declarations under the rule (`Options.rule`), wherever
they come from. `Context.sourceDeps` gives, apart, what a declaration's *source* needs that its
elaborated term does not mention: coercion instances and notation. No hash covers those.

`Context.of env rootPrefix` computes the project's tables once; `Context.depsOf` then gives the lists
of any declarations, extending the walks as it goes, and `Context.closure` walks a graph from some
roots.
-/

open Lean Meta

namespace MeaningGraph

open Hash

/-- Where `Context.closure` stops. -/
inductive Boundary where
  /-- At the project: a declaration from outside it is reached, and not followed. -/
  | project
  /-- Nowhere: the closure follows dependencies into the libraries underneath. -/
  | none
deriving Repr, BEq, Inhabited

/-- How a `Context` analyses. -/
structure Options where
  /-- Where closures stop. -/
  boundary : Boundary := .project
  /-- Which constants are declarations, the nodes of the graphs; the others are looked through. The
  rule `ltb-meaning/1` by default; `Rule.completion` takes what Lean offers for completion. -/
  rule : Rule := .meaning
deriving Inhabited

/-- The dependencies of one declaration, each list without the declaration itself. -/
structure DeclDeps where
  /-- What its statement mentions: the `statement` edges. -/
  statement : Array Name := #[]
  /-- What it means: the `meaning` edges, the graph the meaning hash follows. -/
  meaning : Array Name := #[]
  /-- Everything the kernel checked of it, proofs included: the `term` edges, the graph the content
  hash follows. Empty unless asked for. -/
  term : Array Name := #[]
deriving Repr, Inhabited

/-- The project-wide tables, computed once by `Context.of`, and the two walks, which `Context.depsOf`
extends as it reaches new declarations. -/
structure Context where
  env : Environment
  options : Options := {}
  /-- Root module prefix delimiting the project: a constant is the project's when the module
  declaring it has this prefix (`isProjectLocalConst`). -/
  rootPrefix : Name
  /-- Every constant declared by a project module, as `(name, module, info)`. -/
  constants : Array (Name × Name × ConstantInfo)
  /-- The project's declarations under the rule. -/
  exposed : Std.HashSet Name
  /-- Notation kind ↦ constants its expansion references (`notationExpansionDeps`). -/
  notationDeps : Std.HashMap Name (Array Name)
  /-- Type head constant ↦ coercion instances coercing from it (`coercionInstancesByType`). -/
  coercionInstances : Std.HashMap Name (Array CoercionInstance)
  /-- Project constant ↦ the module declaring it. -/
  declModule : Std.HashMap Name Name
  /-- Project module ↦ the project modules it can see (`visibleProjectModules`). -/
  visibleModules : Std.HashMap Name (Std.HashSet Name)
  /-- The walk that erases proofs: `statement` and `meaning` edges, meaning and local hashes. -/
  meaningWalk : Walk
  /-- The walk that keeps proofs: `term` edges, content hashes. -/
  contentWalk : Walk
  /-- The memo of `Walk.targets` for each walk. -/
  meaningMemo : Std.HashMap Name (Array Name) := {}
  contentMemo : Std.HashMap Name (Array Name) := {}

/-- Scans `env` for the project rooted at `rootPrefix` and builds its tables, with empty walks. -/
def Context.of (env : Environment) (rootPrefix : Name) (options : Options := {}) : Context :=
  let constants := projectConstants env rootPrefix
  let exposed : Std.HashSet Name := constants.foldl (fun acc (name, _, info) =>
    if options.rule.isNode env name info then acc.insert name else acc) {}
  { env, options, rootPrefix, constants, exposed
    notationDeps := notationExpansionDeps env constants
    coercionInstances := coercionInstancesByType env rootPrefix exposed constants
    declModule := constants.foldl (fun acc (name, mod, _) => acc.insert name mod) {}
    visibleModules := visibleProjectModules env rootPrefix
    meaningWalk := Walk.new env options.rule
    contentWalk := Walk.new env options.rule (keepProofs := true) }

/-- Whether `n` is a declaration under the rule: a node of the graphs, where looking through stops. -/
def Context.isNode (ctx : Context) (n : Name) : Bool :=
  match ctx.env.find? n with
  | some info => ctx.options.rule.isNode ctx.env n info
  | none => true

/-- The dependencies of each of `names`, in their order, and the context whose walks now reach them.
`term` says whether to compute the `term` edges, which need the walk that keeps proofs: every proof
term underneath, most of the cost. Runs in `MetaM` over the context's environment. -/
def Context.depsOf (ctx : Context) (names : Array Name) (term : Bool := true) :
    MetaM (Array (Name × DeclDeps) × Context) := do
  let mut ctx := { ctx with meaningWalk := ← ctx.meaningWalk.visit names }
  if term then ctx := { ctx with contentWalk := ← ctx.contentWalk.visit names }
  let mut out := #[]
  for n in names do
    let ((statement, meaning), memo) := ctx.meaningWalk.edges n ctx.meaningMemo
    ctx := { ctx with meaningMemo := memo }
    let mut termDeps := #[]
    if term then
      let ((_, t), memo) := ctx.contentWalk.edges n ctx.contentMemo
      ctx := { ctx with contentMemo := memo }
      termDeps := t
    out := out.push (n, { statement, meaning, term := termDeps })
  return (out, ctx)

/-- The dependencies of every declaration of the project, in environment order. -/
def Context.allDeclDeps (ctx : Context) (term : Bool := true) :
    MetaM (Array (Name × DeclDeps) × Context) :=
  ctx.depsOf (ctx.constants.filterMap fun (n, _, _) => if ctx.exposed.contains n then some n else none)
    term

/-- What the declaration's *source* needs that its elaborated term does not mention: the coercion
instances whose coerced-from type the declaration mentions in full (anywhere, proofs included), and,
for a notation, the constants it expands to. Looked through helpers, deduplicated, and kept only when
the declaration's module can see them; the updated cache is returned alongside.

These are the `source` dependencies: what a standalone file must bring along to elaborate. They are
not part of what a declaration means, and no hash covers them. -/
def Context.sourceDeps (ctx : Context) (cache : Cache) (name : Name) (info : ConstantInfo) :
    Array Name × Cache :=
  let used := usedConstantsOf ctx.env name info true
  let present : Std.HashSet Name := used.foldl (fun acc c => acc.insert c) {}
  let coercions := used.foldl (init := #[]) fun acc c =>
    acc ++ (ctx.coercionInstances.getD c #[]).filterMap fun inst =>
      if inst.witnesses.all present.contains then some inst.name else none
  let (expanded, cache) :=
    expandThrough ctx.env (!ctx.isNode ·) cache (coercions ++ ctx.notationDeps.getD name #[])
  let visible := ctx.visibleModules.getD (ctx.declModule.getD name .anonymous) {}
  let out := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut out := #[]
    for dep in expanded do
      if dep == name || seen.contains dep then continue
      seen := seen.insert dep
      let importable := match ctx.declModule.get? dep with
        | none => true
        | some mod => visible.contains mod
      if importable then out := out.push dep
    return out
  (out, cache)

/-! ## Closures -/

/-- The graph `Context.closure` follows. A proof contributes its statement under each: what a theorem
rests on is what it states, not what its proof happened to call. -/
inductive Follow where
  /-- The `statement` edges. -/
  | statement
  /-- The `meaning` edges. -/
  | meaning
  /-- The `term` edges: a definition is followed whole, the lemmas its proofs call included, as
  [trust](https://github.com/chrisflav/trust) draws it. -/
  | term
deriving Repr, BEq, Inhabited

/-- A declaration `Context.closure` reached, with its dependencies. -/
structure Reached where
  name : Name
  /-- Whether it is a proof: a theorem, or a declaration whose type is a proposition. -/
  isProp : Bool
  /-- Its dependencies: empty for a declaration outside the project under `Boundary.project`, and
  `term` only for what is not a proof, under `Follow.term`. -/
  deps : DeclDeps
deriving Inhabited

/-- The dependencies `follow` takes out of `r`. -/
def Follow.targets (follow : Follow) (r : Reached) : Array Name :=
  if r.isProp then r.deps.statement
  else match follow with
    | .statement => r.deps.statement
    | .meaning => r.deps.meaning
    | .term => r.deps.term

/-- Whether the declaration `info` is a proof: a theorem, or one whose type is a proposition. -/
def isProofDecl (info : ConstantInfo) : MetaM Bool := do
  if info matches .thmInfo _ then return true
  try Meta.isProp info.type catch _ => return false

/-- Every declaration reachable from `roots` along `follow`, with its dependencies: breadth-first, a
level at a time. The roots come first, then each level in the order it was reached. Under
`Boundary.project` a declaration from outside the project is reached and not followed. Also returns
the context, whose walks now reach everything the closure did. -/
def Context.closure (ctx : Context) (roots : Array Name) (follow : Follow := .meaning) :
    MetaM (Array Reached × Context) := do
  let mut ctx := ctx
  let mut seen : Std.HashSet Name := {}
  let mut frontier : Array Name := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      frontier := frontier.push r
  let mut out : Array Reached := #[]
  while !frontier.isEmpty do
    let known := frontier.filterMap fun n => (ctx.env.find? n).map (n, ·)
    let props ← known.mapM fun (_, info) => isProofDecl info
    let followed (n : Name) := ctx.options.boundary == .none || ctx.declModule.contains n
    let proofs := (known.zip props).filterMap fun ((n, _), p) => if p && followed n then some n else none
    let data := (known.zip props).filterMap fun ((n, _), p) => if !p && followed n then some n else none
    let (ofProofs, c) ← ctx.depsOf proofs (term := false)
    let (ofData, c) ← c.depsOf data (term := follow == .term)
    ctx := c
    let byName : Std.HashMap Name DeclDeps := (ofProofs ++ ofData).foldl (fun m (n, d) => m.insert n d) {}
    let mut next := #[]
    for ((name, _), isProp) in known.zip props do
      let r : Reached := { name, isProp, deps := byName.getD name {} }
      out := out.push r
      for t in follow.targets r do
        unless seen.contains t do
          seen := seen.insert t
          next := next.push t
    frontier := next
  return (out, ctx)

/-- One-shot entry point: the dependencies of every declaration of the project rooted at
`rootPrefix`, in `MetaM` over `env`. -/
def declDepsOf (env : Environment) (rootPrefix : Name) (term : Bool := true) :
    MetaM (Array (Name × DeclDeps)) :=
  return (← (Context.of env rootPrefix).allDeclDeps term).1

end MeaningGraph
