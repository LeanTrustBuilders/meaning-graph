# MeaningGraph

What every declaration of a Lean project rests on: the constants its **type** uses, and the
constants its type **and body** use — computed from the compiled environment, with the four things
an elaborated term silently drops put back.

Depends on Lean core and nothing else — no Lake, no document format, no notion of a "project
directory" or of an output. It began inside the
[`exposition`](https://github.com/LeanMachineLearning/exposition) repository, whose `referee` tool
is its first consumer, and is a package of its own precisely so that using the analysis does not
drag in that tool's build (Verso, SubVerso, MD4Lean, …). It moved from `RemyDegenne/meaning-graph`
to the [LeanTrustBuilders](https://github.com/LeanTrustBuilders) organization, with its history
and tags; the LeanTrustBuilders extractor (`trust-extract`) is its other consumer.

## Why not just `Expr.getUsedConstants`

Because the elaborated type and value of a declaration under-report what its *source* needs, in four
ways this library compensates for:

- **Compiler-generated helpers** — `_proof_N`, `match_N`, structure field defaults, well-founded
  recursion helpers — are constants of the project itself, but nobody wrote them, and stopping at
  such a name hides what it in turn depends on. `expandThroughInternals` recurses *through* them,
  and only through them, so the answer is stated in terms of declarations a human wrote.
- **`Expr.proj` nodes**: `Expr.foldConsts` walks through a projection without ever offering the
  structure name it carries. `projStructureNames` recovers those names.
- **Notation**: a notation's macro stores the constants it expands to as pre-resolved `Name` *data*
  inside embedded `Syntax`, invisible to a constant walk. `notationExpansionDeps` reconstructs them.
- **Coercions**: an elaborated term keeps only the underlying `@[coe]` function and drops the
  instance — yet the instance is what makes the source's `↑`/`⇑` elaborate.
  `coercionInstancesByType` recovers it.

## Use

Add the dependency:

```toml
# lakefile.toml
[[require]]
name = "MeaningGraph"
git = "https://github.com/LeanTrustBuilders/meaning-graph"
rev = "main"
```

```lean
-- lakefile.lean
require MeaningGraph from git "https://github.com/LeanTrustBuilders/meaning-graph" @ "main"
```

Then, given an `Environment` with the project's modules imported and the root module prefix that
delimits it:

```lean
import MeaningGraph

open Lean MeaningGraph

def report (env : Environment) : IO Unit := do
  for (name, d) in declDepsOf env `MyLibrary do
    IO.println s!"{name}: {d.typeDeps.size} in the statement, {d.deps.size} in all"
```

`declDepsOf` is the one-shot form. For anything beyond a single pass, build the project-wide tables
once and reuse them, since that is where the whole-environment work happens:

```lean
let ctx := Context.of env `MyLibrary
let graph := ctx.allDeclDeps              -- Array (Name × DeclDeps)
```

`Context.declDeps` answers per declaration, threading an explicit `Cache`, when you want to drive
the iteration yourself. `Context.depsOf` answers for a list of declarations, in parallel chunks, and
gives the same result as `declDeps` on each in turn; `allDeclDeps` is `depsOf` on every exposed
declaration.

Both take a `DepsRequest` saying which lists to compute. `deps` walks the whole value, every proof
term included, which is most of the cost; a caller that only needs what declarations mean asks for
`{ deps := false }`:

```lean
let ctx ← (Context.of env `MyLibrary).withDataValueConsts
let meanings := ctx.depsOf targets { deps := false }   -- typeDeps and dataDeps only
```

### What you get per declaration

`DeclDeps` has three fields, and the difference between them is the point:

- `typeDeps` — what the **statement** mentions. For a theorem this is what a reader has to
  understand to know what was claimed.
- `deps` — the statement **and** the proof or body.
- `dataDeps` — the statement and the body's *data*, with the proofs embedded inside the value
  skipped. Equal to `deps` unless you asked for the extra analysis with
  `(← Context.of env root |>.withDataValueConsts)`, which needs `MetaM` because deciding whether a
  constructor field is `Prop`-valued is a typing question. This is the field that says what a
  bundled structure instance *means*, without the lemmas its `left_inv` obligation happened to call.

### Graph passes

`reverseDeps` (who uses this) and `transitiveDeps` / `topologicalClosure` (everything this reaches,
each dependency before its first use) are stated over plain `Name`-keyed maps rather than over
`DeclDeps`, so the caller decides which edges count *before* running them:

```lean
-- Treat a theorem's proof as opaque; take the full body for everything else.
let edges := graph.map fun (n, d) =>
  (n, if (env.find? n).any (· matches .thmInfo _) then d.typeDeps else d.deps)
let users := reverseDeps edges
```

The topological order is the order the declarations could be emitted into a single self-contained
file. Cycles (mutual recursion) are tolerated rather than rejected.

## Versions

`main` follows the newest Lean toolchain, and a tag is created for each toolchain it moves to
(`v4.35.0-rc2`, …). A tag is a snapshot: the fixes above came after `v4.34.0` and `v4.35.0-rc2`
were tagged. For a project on an older toolchain, a branch `lean-v<toolchain>` carries the current
code on that toolchain (`lean-v4.34.0`, for Tau Ceti).

## Scope and limits

- The analysis is over the **compiled environment**, not over source text. It sees what the
  elaborator produced, which is why the four recoveries above exist at all — and it cannot see a
  dependency that leaves no trace in the environment.
- `rootPrefix` is what bounds the work: a constant is the project's own when the module declaring it
  carries that prefix. Everything upstream is reported as a leaf and never expanded, so the cost is
  proportional to your project, not to Mathlib.
- Which declarations count as "the project's own user-written declarations" is `shouldExpose`.
  Expansion stops at those; everything else generated by the compiler is looked through.

## Performance

On a quarter of Tau Ceti (63,486 project constants over 9,631 imported modules, of which 20,129
declarations to analyse), `Context.of` takes 0.3 s and the dependencies take 0.6 s. Before, the
same took 33 s and 51 s, and on one commit the notation walk alone did not finish in 18 minutes.
Three things made the difference, each checked to change no result (the LeanTrustBuilders extractor
writes byte-identical datasets of Tau Ceti with the old and the new code):

- `moduleNameOf` indexes `env.header.modules` directly. `env.header.moduleNames` rebuilds the array
  of every module's name on each call, about 170 µs on such an environment against 50 ns for the
  lookup, and the classification calls it once per constant: 11 seconds, twice over, in `Context.of`
  alone.
- The notation walk (`collectEmbeddedNames`) visits each shared subterm once, and only values that
  build a `Name` are walked at all (`buildsName`). A plain tree walk visits a shared subterm once per
  path to it: on one Tau Ceti commit it ran for more than 18 minutes without finishing.
- Dependency lists are deduplicated with a hash set, not `Array.contains`, and `depsOf` runs in
  parallel.

## Checks

The library ships two targets of its own, both checked at elaboration time — building them is
running them:

- `lake build MeaningGraphTest` — `#guard` unit checks of the name classification, the `Expr`-level
  constant collection, the notation and coercion recoveries, and the graph passes; and, in
  `MeaningGraph.TestEquivalence`, the fast notation walk and the parallel driver against the
  original implementations, on `Init.Notation` and `Init.Data.List`, plus a term with 2⁶⁴ paths
  that only a walk visiting each subterm once gets through.
- `lake build MeaningGraphProofs` — theorems about the project boundary (`hasPrefixName` is a
  component-wise prefix order; `isInternalName` is inherited downwards) and about
  `topologicalClosure`, which is total rather than `partial`.

Both live under `MeaningGraph/` as `MeaningGraph.Test` and `MeaningGraph.Proofs` rather than at the
top level: module roots are shared across a whole Lake workspace, so a package that claims `Test`
takes that name away from every project that requires it.
