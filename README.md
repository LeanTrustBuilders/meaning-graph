# MeaningGraph

What every declaration of a Lean project rests on: the constants its **statement** uses, and those its
statement **and body** use, computed from the compiled environment, with the four things an elaborated
term drops put back. And, from the same walk, a hash of what each declaration means.

It depends on Lean core only: no Lake, no output format.

## Why not `Expr.getUsedConstants`

The elaborated type and value of a declaration under-report what its source needs, in four ways:

- **Compiler-generated helpers** (`_proof_N`, `match_N`, structure field defaults, well-founded
  recursion helpers) are constants nobody wrote. `expandThrough` recurses through them, and only
  them, so the answer is in terms of declarations a person wrote.
- **`Expr.proj` nodes** carry a structure name that `Expr.foldConsts` never offers.
  `projStructureNames` recovers it.
- **Notation** stores the constants it expands to as `Name` data inside embedded `Syntax`.
  `notationExpansionDeps` reconstructs them.
- **Coercions**: an elaborated term keeps the `@[coe]` function and drops the instance that made
  `↑`/`⇑` elaborate. `coercionInstancesByType` recovers it.

## Use

```toml
# lakefile.toml
[[require]]
name = "MeaningGraph"
git = "https://github.com/LeanTrustBuilders/meaning-graph"
rev = "main"
```

Given an `Environment` with the project imported and the root module prefix that delimits it, in
`MetaM` over that environment:

```lean
import MeaningGraph
open Lean MeaningGraph

def report : MetaM Unit := do
  for (name, d) in ← declDepsOf (← getEnv) `MyLibrary do
    IO.println s!"{name}: {d.statement.size} in the statement, {d.term.size} in all"
```

`declDepsOf` is the one-shot form. `Context.of env root` builds the project's tables once;
`Context.depsOf ctx names` gives the dependencies of any declarations and returns the context, whose
walks now reach them, for the next call. `(term := false)` skips the `term` list, which walks every
proof underneath, most of the cost.

### Per declaration

`DeclDeps` has three lists, each the edges of one of the walks of `MeaningGraph.Hash`, so each hash
follows its graph:

- `statement`: what the **statement** mentions, proofs erased: what a reader must understand to know
  what is claimed;
- `meaning`: what the declaration **means**, proofs erased everywhere: a proof's statement, a
  definition's statement and value, an inductive type's types and constructors. The meaning hash
  follows this graph;
- `term`: everything the kernel checked of it, **proofs included**. The content hash follows this
  graph.

Each looks through helpers wherever they come from, so its targets are declarations.

### Rules and closures

`Options` says which constants are declarations (`rule`) and where closures stop (`boundary`):

```lean
let ctx := Context.of env `MyLibrary { boundary := .none, rule := .completion }
```

- `rule := .meaning` (the default): a declaration is one a person wrote, private ones included.
  `rule := .completion`: what Lean offers for completion (`Lean.Meta.allowCompletion`),
  constructors, projections and generated lemmas included. The meaning hash is the same under both;
  only the graph's nodes differ.
- `boundary := .none`: closures follow dependencies into the libraries underneath; with the default
  `.project`, a declaration from outside the project is reached and not followed.

`Context.closure` walks a graph from some roots, a level at a time, along a `Follow`: `.statement`,
`.meaning` or `.term`. A proof always contributes only its statement, so along `.term` a definition
is followed whole, the lemmas its proofs call included, and a lemma contributes what it states.

```lean
let (reached, ctx) ← ctx.closure roots .term    -- Array Reached: name, isProp, deps
```

`Context.sourceDeps` gives, separately, what a declaration's source needs besides its elaborated
term: coercion instances and notation. No hash covers these.

### `MeaningGraph.Hash`: one rule for the graph and the hash

`import MeaningGraph.Hash` gives what a declaration's meaning rests on and a hash of it, from one walk
under one rule (`ltb-meaning/1`), so the two agree by construction:

- **Proofs are erased everywhere**, in types, values and helpers: an argument whose expected type is a
  proposition, and a let-bound value whose type is one, become a marker. A declaration whose type is
  a proposition means its statement.
- **Content**: a definition's type and erased value; a theorem's, axiom's or opaque constant's type;
  an inductive type with its mutual block and constructors. A constructor or recursor stands for its
  block.
- **Declarations** are those a person wrote, private ones included (`isDeclaration`; the rule is a
  parameter, `Rule.isNode`). Everything else is looked through.
- **The meaning hash** replaces each reference in a constant's content by the referenced constant's
  meaning hash (a Merkle hash, well founded since the kernel only allows references to earlier
  constants or the same block). It covers everything underneath, Lean core included, and does not
  depend on names, binder names or binder kinds.
- **Edges** (`Walk.edges`) go to the declarations a content mentions, through helpers.
- **The local hash** (`Walk.localHash`) is the same content with references to other declarations by
  name: it changes when the declaration itself is rewritten.
- **The content hash** (`ltb-content/1`: `Walk.new env (keepProofs := true)`, then `Walk.content?`)
  erases nothing: it covers everything the kernel checked, proofs included, and moves when a proof
  anywhere underneath changes.

So a declaration's meaning hash changes exactly when something in its `meaning` closure changes, and
its content hash exactly when something in its `term` closure does (up to 64-bit collisions), whatever
the rule's nodes.

### Graph passes

`reverseDeps` (who uses this), and `transitiveDeps` and `topologicalClosure` (everything this reaches,
each dependency before its first use), work on plain `Name`-keyed maps, so the caller chooses the
edges first:

```lean
-- A theorem's proof is opaque; take the full body for everything else.
let edges := graph.map fun (n, d) =>
  (n, if (env.find? n).any (· matches .thmInfo _) then d.statement else d.term)
let users := reverseDeps edges
```

Cycles (mutual recursion) are tolerated.

## Scope and limits

- The analysis is over the compiled environment, not the source: it cannot see a dependency that
  leaves no trace in the environment.
- The walks go down to Lean core, since a hash covers everything underneath: the cost grows with
  what the declarations rest on, and `term` with every proof underneath.
- `rootPrefix` says which constants are the project's: those of the modules with that prefix.

## Versions

`main` follows the newest Lean toolchain. A branch `lean-v<toolchain>` carries the same code on an
older one (`lean-v4.34.0`). The tags `v4.34.0` and `v4.35.0-rc2` are older snapshots.

## Checks

Both targets are checked at elaboration time: building them runs them.

- `lake build MeaningGraphTest`: the name classification, constant collection, notation and coercion
  recoveries and graph passes (`MeaningGraph.Test`); the notation walk against a reference
  implementation, including a term with 2⁶⁴ paths (`TestEquivalence`); the rules, the three lists and
  the closures on Lean core (`TestOptions`); and the hashes (`TestHash`): proofs, binder names and
  constant names left out, and a change moving exactly the hashes of what rests on it along the
  hash's graph, meaning and content alike.
- `lake build MeaningGraphProofs`: theorems about the project boundary and about
  `topologicalClosure`, which is total.

The test modules live under `MeaningGraph/`: module roots are shared across a Lake workspace, so a
package claiming `Test` would take that name from every project requiring it.
