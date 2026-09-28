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

Given an `Environment` with the project imported and the root module prefix that delimits it:

```lean
import MeaningGraph
open Lean MeaningGraph

def report (env : Environment) : IO Unit := do
  for (name, d) in declDepsOf env `MyLibrary do
    IO.println s!"{name}: {d.typeDeps.size} in the statement, {d.deps.size} in all"
```

`declDepsOf` is the one-shot form. Beyond a single pass, build the project-wide tables once:

```lean
let ctx := Context.of env `MyLibrary
let graph := ctx.allDeclDeps              -- Array (Name × DeclDeps)
```

`Context.declDeps` answers for one declaration, with an explicit `Cache`; `Context.depsOf` answers for
many, in parallel, with the same result. Both take a `DepsRequest`: `deps` walks every proof term,
which is most of the cost, so a caller that needs only what declarations mean asks for
`{ deps := false }`.

### Per declaration

`DeclDeps` has three lists:

- `typeDeps`: what the **statement** mentions, what a reader must understand to know what is claimed;
- `deps`: the statement and the whole proof or body;
- `dataDeps`: the statement and the body's *data*, skipping the proofs inside the value. It needs
  `(← Context.of env root |>.withDataValueConsts)` (in `MetaM`, since whether a field is
  `Prop`-valued is a typing question), and otherwise equals `deps`. It says what a bundled instance
  means, without the lemmas its proof fields call.

### Past the project, and other graphs

By default the analysis stops at the project (an upstream constant is a leaf) and a declaration is
one a person wrote (`isAuthored`). `Options` changes both:

```lean
let ctx := Context.of env `MyLibrary { boundary := .none, display := .completion }
```

- `boundary := .none`: any declaration of the environment can be analyzed, and helpers are looked
  through wherever they come from.
- `display := .completion`: a declaration is what Lean offers for completion
  (`Lean.Meta.allowCompletion`), constructors, projections and generated lemmas included.

`Context.closure` walks the graph from some roots, a level at a time in parallel, along a `Follow`
rule; a proof always contributes only its statement:

- `.statement` follows statements;
- `.meaning` follows statements and the data of definitions' values (`dataDeps`);
- `.term` follows everything a definition's value mentions (`deps`), the lemmas its proofs call
  included.

```lean
let (reached, ctx) ← ctx.closure roots .term    -- Array Reached: name, info, isProp, deps
```

Past the project, the notation and coercion recoveries apply to the project's own declarations only.

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
- **Edges** (`Walk.targets`) go to the declarations a content mentions, through helpers.
- **The local hash** (`Walk.localHash`) is the same content with references to other declarations by
  name: it changes when the declaration itself is rewritten.
- **The content hash** (`ltb-content/1`: `Walk.new env (keepProofs := true)`, then `Walk.content?`)
  erases nothing: it covers everything the kernel checked, proofs included, and moves when a proof
  anywhere underneath changes.

So a declaration's meaning hash changes exactly when something in its closure along the edges
changes (up to 64-bit collisions). `Context.sourceDeps` gives, separately, what a declaration's
source needs besides its meaning: coercion instances and notation.

### Graph passes

`reverseDeps` (who uses this), and `transitiveDeps` and `topologicalClosure` (everything this reaches,
each dependency before its first use), work on plain `Name`-keyed maps, so the caller chooses the
edges first:

```lean
-- A theorem's proof is opaque; take the full body for everything else.
let edges := graph.map fun (n, d) =>
  (n, if (env.find? n).any (· matches .thmInfo _) then d.typeDeps else d.deps)
let users := reverseDeps edges
```

Cycles (mutual recursion) are tolerated.

## Scope and limits

- The analysis is over the compiled environment, not the source: it cannot see a dependency that
  leaves no trace in the environment.
- `rootPrefix` bounds the work: a constant is the project's own when its module has that prefix. By
  default the cost is proportional to the project, not to what it imports; `Boundary.none` makes it
  proportional to what the closure reaches.
- Which declarations are the project's own user-written ones is `shouldExpose`; everything else is
  looked through.

## Versions

`main` follows the newest Lean toolchain. A branch `lean-v<toolchain>` carries the same code on an
older one (`lean-v4.34.0`). The tags `v4.34.0` and `v4.35.0-rc2` are older snapshots.

## Checks

Both targets are checked at elaboration time: building them runs them.

- `lake build MeaningGraphTest`: the name classification, constant collection, notation and coercion
  recoveries and graph passes (`MeaningGraph.Test`); the fast walks and the parallel driver against
  reference implementations, including a term with 2⁶⁴ paths (`TestEquivalence`); the options and
  closures (`TestOptions`); and the hashes (`TestHash`): proofs, binder names and constant names left
  out, and a change moving exactly the hashes of what rests on it, on two versions of a small library.
- `lake build MeaningGraphProofs`: theorems about the project boundary and about
  `topologicalClosure`, which is total.

The test modules live under `MeaningGraph/`: module roots are shared across a Lake workspace, so a
package claiming `Test` would take that name from every project requiring it.
