module

public import Lean
public import Lean.Meta.Instances

@[expose] public section

/-!
# Dependency analysis for the declarations of a Lean project

Computes, for every declaration of a project, which constants its *type* uses (`DeclDeps.typeDeps`)
and which its type *and* body use (`DeclDeps.deps`), plus the graph-level passes that run on the
result: reverse edges and transitive closure in topological order.

This module depends on Lean core only — no Lake, no document format, no notion of a "project
directory" or of output — so it can be reused by any tool that needs to know what a declaration
rests on.

## Why not just `Expr.getUsedConstants`?

The elaborated type and value of a declaration under-report what its *source* needs, in four ways
this module compensates for:

* **compiler-generated helpers** (`_proof_N`, `match_N`, structure field defaults, well-founded
  recursion helpers) are constants of the project itself, but nobody wrote them; stopping at such a
  name hides what it in turn depends on. `expandThroughInternals` recurses through them, and only
  through them.
* **`Expr.proj` nodes**: through Lean 4.33, `Expr.foldConsts` walked *through* a projection without
  ever offering the structure name it carries; core reports it itself since 4.34.
  `projStructureNames` remains as the proven statement of that recovery, and a guard in
  `Test/Deps.lean` pins core's fix.
* **notation**: a notation's macro stores the constants it expands to as pre-resolved `Name` *data*
  inside embedded `Syntax`, invisible to a constant walk. `notationExpansionDeps` reconstructs them.
* **coercions**: an elaborated term keeps only the underlying `@[coe]` function and drops the
  instance, yet the instance is what makes the source's `↑`/`⇑` elaborate.
  `coercionInstancesByType` recovers it.

## Entry points

`Context.of env rootPrefix` computes the project-wide tables once; `Context.declDeps` then answers
per declaration, threading a memo cache, and `Context.depsOf` answers for many declarations in
parallel. `DepsRequest` says which lists to compute. `declDepsOf` wraps it all for the common
"give me everything" case.

The graph passes (`reverseDeps`, `transitiveDeps`) are deliberately stated over plain `Name`-keyed
maps rather than over any declaration record, so a caller can decide which edges count (e.g.
type-only edges for theorems) before running them.
-/

open Lean
open Lean.Meta

namespace MeaningGraph

/-! ## Name classification

Which constants are the project's own user-written declarations, and which are compiler output.
This is what bounds the analysis: helper constants are expanded *through* (their dependencies are
pulled in instead of the helper), and everything outside the project is left alone.
-/

/-- True if `s` is `pfx` followed by a non-empty sequence of digits, the naming convention used
by the compiler for auto-generated declarations like `match_1`, `eq_2`, `hcongr_11`. -/
def isPrefixWithDigitSuffix (pfx s : String) : Bool :=
  s.startsWith pfx &&
    let rest := s.drop pfx.length
    !rest.isEmpty && rest.toString.toList.all Char.isDigit

/-- True if `s` is a single name component the compiler generates: anything underscore-led
(`_hyg`, `_proof_3`, `_private`, ...), a `match_<n>`/`eq_<n>`/`hcongr_<n>` helper, or the
equation-lemma names `eq_def`/`eq_unfold`. -/
def isAuxComponent (s : String) : Bool :=
  s.startsWith "_"
    || isPrefixWithDigitSuffix "match_" s
    || isPrefixWithDigitSuffix "eq_" s || s == "eq_def" || s == "eq_unfold"
    || isPrefixWithDigitSuffix "hcongr_" s

/-- Auto-generated companion names that Lean exposes *no* dedicated environment predicate for, so
they can only be recognized by their (stable) spelling. A name *any* of whose components matches is
treated as internal, matched at every component (not just the last) so helpers nested under an
already-internal name (e.g. `Foo.match_1.eq_1`) are caught too.

This list is deliberately the residual left after `shouldExpose` first consults everything Lean
*does* know directly:
* the recursor family (`rec`, `recOn`, `casesOn`, `brecOn`, `below`, `binductionOn`, ...) →
  `ConstantInfo.recInfo` and `isAuxRecursor`;
* `noConfusion` → `isNoConfusion` (note: its `noConfusionType` sibling is *not* covered by that
  predicate, hence it remains here);
* constructor companions (`mk.inj`, `mk.injEq`, `mk.sizeOf_spec`, ...) → `hasConstructorPrefix`,
  which keys on `ctorInfo` rather than on the string `mk`, so a user declaration named `Foo.mk`
  (a structure whose real constructor was renamed to free up `mk`) or a legitimate theorem such as
  `Kernel.prodMkLeft_inj` is never mistaken for compiler output.

What is left here are companions Lean attaches to *ordinary* declarations (not just constructors)
or to types without flagging them: `congr_simp` (added to defs and inductives alike), the `@[ext]`
lemma `ext_iff`, the induction principle `ind`, the constructor-index helper `ctorIdx`, and
`noConfusionType`.

`noConfusionType`, `ctorIdx`, and `congr_simp` were each observed leaking on a Mathlib-backed test
project when removed. `ind` and `ext_iff` were *not* exercised by that project (no Prop inductive's
`.ind` nor any `@[ext]` structure surfaced one), but they are standard generated companions and are
kept here so the analysis stays correct on projects that do use them. -/
def internalComponentNames : List String :=
  ["noConfusionType", "ind", "ctorIdx", "ext_iff", "congr_simp"]

/-- True if any component of `name` is an auxiliary component (`isAuxComponent`) or one of the
compiler's auto-generated companion names (`internalComponentNames`). -/
def isInternalName : Name → Bool
  | .anonymous => false
  | .num p _ => isInternalName p
  | .str p s =>
      isAuxComponent s
      || s ∈ internalComponentNames
      || isInternalName p

/-- True when some strict prefix of `name` is the name of a constructor in `env`, i.e. `name` lives
inside a constructor's namespace. Everything Lean places there (`S.mk.inj`, `S.mk.injEq`,
`S.mk.sizeOf_spec`, ...) is auto-generated and should be hidden.

This keys on the environment's `ctorInfo` rather than on the spelling of the prefix, so it hides
these companions for *any* constructor name (`mk`, a custom `intro`, ...) while leaving a user
declaration that merely happens to be named like a constructor (its prefix is not a `ctorInfo`)
untouched. -/
def hasConstructorPrefix (env : Environment) (name : Name) : Bool :=
  go name.getPrefix
where
  -- Matching the two non-empty constructors rather than calling `getPrefix` makes the recursion
  -- structural, so this needs no `partial`. Same function: `(.str p _).getPrefix = p`.
  go : Name → Bool
    | .anonymous => false
    | .str p s =>
      (match env.find? (.str p s) with | some (.ctorInfo _) => true | _ => false) || go p
    | .num p i =>
      (match env.find? (.num p i) with | some (.ctorInfo _) => true | _ => false) || go p

/-- True if `prefixName` is `n` itself or one of its dotted ancestors. This is a *component-wise*
test, not a string prefix: the name `LMLExtra.Foo` does *not* have prefix `LML`. -/
def hasPrefixName (n prefixName : Name) : Bool :=
  n == prefixName || match n with
    | .str p _ => hasPrefixName p prefixName
    | .num p _ => hasPrefixName p prefixName
    | .anonymous => false

/-- The module `name` was declared in, if `env` records one (declarations added to the current
module, rather than imported, have no module index).

Reads `env.header.modules` at the index, not `env.header.moduleNames`: the latter builds the array of
every module's name on each call, which on a Mathlib-sized environment (10,000 modules) costs about
170 µs, against 50 ns for the lookup itself. Every classification below calls this once per
constant, and `expandThroughInternals` once per constant it visits. -/
def moduleNameOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  return (← env.header.modules[idx.toNat]?).module

/-- True if `name` is defined in a project module (one whose name has `rootPrefix` as a prefix).
This is keyed on the declaration's *module*, not its name: a project's declaration names need not
share the root module prefix (e.g. module `LeanMachineLearning.…` declaring `Bandits.foo`). -/
def isProjectLocalConst (env : Environment) (rootPrefix : Name) (name : Name) : Bool :=
  (moduleNameOf env name).any (hasPrefixName · rootPrefix)

/-- Whether a declaration is one a person wrote, as opposed to compiler output: not a recursor,
projection, constructor or constructor companion, `noConfusion`, hygienic or otherwise internal
helper. Says nothing about where the declaration comes from; `shouldExpose` adds that. -/
def isAuthored (env : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  if env.isProjectionFn name then
    false
  else if isInternalName name || name.isInternal || name.isImplementationDetail then
    false
  else if isAuxRecursor env name || isNoConfusion env name then
    false
  else if hasConstructorPrefix env name then
    false
  else match info with
    | .ctorInfo _ | .recInfo _ | .quotInfo _ => false
    | _ => true

/-- Decides whether a declaration is one the project's author actually wrote, as opposed to
compiler output (recursors, projections, constructor companions, hygienic helpers, ...) or a
declaration from outside the project. This is both the set a consumer would display and the
boundary at which dependency expansion stops (see `expandThroughInternals`). -/
def shouldExpose (env : Environment) (rootPrefix : Name) (name : Name) (info : ConstantInfo) : Bool :=
  isProjectLocalConst env rootPrefix name && isAuthored env name info

/-- Whether Lean offers `name` for completion, and it is not an internal detail: the rule
[aftk](https://github.com/mathlib-initiative/aftk)'s `shouldDisplay` states, which
[trust](https://github.com/chrisflav/trust) draws its graphs with. Unlike `isAuthored`, it keeps
constructors, projections, `Quot` primitives and the lemmas Lean generates under ordinary names
(`eq_1`, `eq_def`, `injEq`, `ext_iff`, …). -/
def isCompletionVisible (env : Environment) (name : Name) : Bool :=
  Lean.Meta.allowCompletion env name && !(privateToUserName name).isInternalDetail

/-! ## Options: where the analysis stops, and which constants are declarations

The defaults are this module's own choices: a project's analysis stops at the project, and the
declarations are those a person wrote. Other tools draw their graphs differently —
[trust](https://github.com/chrisflav/trust) follows dependencies into the libraries underneath and
counts every constant completion offers — and `Options` lets a caller have those choices without
another dependency computation.
-/

/-- Where the analysis stops. -/
inductive Boundary where
  /-- At the project. A constant from outside it is a leaf, reported as itself, and only the
  project's own helpers are looked through. -/
  | project
  /-- Nowhere. An upstream declaration can be analysed as a project one is (`Context.declDeps`
  accepts it), helpers are looked through wherever they come from, and `Context.closure` follows
  dependencies into the libraries underneath. -/
  | none
deriving Repr, BEq, Inhabited

/-- Which constants are declarations in their own right: nodes of the graph, and where looking
through helpers stops. Every other constant is looked through. -/
inductive Display where
  /-- Those a person wrote (`isAuthored`). -/
  | authored
  /-- Those Lean offers for completion (`isCompletionVisible`): trust's rule. -/
  | completion
deriving Repr, BEq, Inhabited

/-- Whether `name` is a declaration under `display`. -/
def Display.accepts (display : Display) (env : Environment) (name : Name) (info : ConstantInfo) :
    Bool :=
  match display with
  | .authored => isAuthored env name info
  | .completion => isCompletionVisible env name

/-- How a `Context` analyses. -/
structure Options where
  boundary : Boundary := .project
  display : Display := .authored
deriving Repr, Inhabited

/-- All constants belonging to modules whose name has `rootPrefix`, paired with their module
name, gathered directly from `env.header.moduleData` so that the (typically much larger) set of
constants from imported libraries is never iterated.

Each name appears exactly once, attributed to the module `env.getModuleIdxFor?` records for it.
That is not redundant with walking the per-module tables: two modules that are never imported into
each other can both declare the same name (observed as a lemma copy-pasted between two `ForMathlib`
files of disjoint subtrees, which `lake build` accepts), and then the name sits in both modules'
`constNames`. Every downstream consumer is name-keyed — page tags, extracted file stems,
`declByName`, and the environment queries for docstrings, ranges and dependencies — so the walk
must pick one occurrence, and it must pick the *same* one those env queries answer for, or the
declaration would be attributed to one module and sourced from another. -/
def projectConstants (env : Environment) (rootPrefix : Name) : Array (Name × Name × ConstantInfo) :=
  (Array.range env.header.modules.size).foldl (fun acc idx =>
    let modName := env.header.modules[idx]!.module
    if hasPrefixName modName rootPrefix then
      let data := env.header.moduleData[idx]!
      (Array.zip data.constNames data.constants).foldl
        (fun acc2 (cname, cinfo) =>
          if moduleNameOf env cname == some modName then acc2.push (cname, modName, cinfo)
          else acc2) acc
    else acc) #[]

/-- Names declared in more than one project module, with the modules that carry them; see
`projectConstants`, which keeps a single occurrence of each. Exposed separately so `collect` can
say which copies the site will not show, instead of dropping them silently. -/
def duplicatedProjectConstants (env : Environment) (rootPrefix : Name) : Array (Name × Array Name) :=
  let byName := (Array.range env.header.modules.size).foldl (init := ({} : Std.HashMap Name (Array Name)))
    fun acc idx =>
      let modName := env.header.modules[idx]!.module
      if hasPrefixName modName rootPrefix then
        env.header.moduleData[idx]!.constNames.foldl
          (fun acc2 cname => acc2.insert cname ((acc2.getD cname #[]).push modName)) acc
      else acc
  byName.toArray.filter (·.2.size > 1) |>.qsort (fun a b => a.1.toString < b.1.toString)

/-! ## Constants used by an expression -/

/-- Every structure name carried by an `Expr.proj` node inside `e`, in traversal order and
possibly with repeats (all consumers dedup).

Up to Lean 4.33, `Expr.getUsedConstants` did *not* report these: its underlying `Expr.foldConsts`
recursed through a `.proj S i b` node into `b` without ever offering `S`. So a structure that an
elaborated term reaches only by projecting one of its fields — never by naming it — was absent
from the constant list, and `exprUsedConstants` existed to append this recovery. Core closed the
gap in 4.34 — `foldConsts` now visits the `.proj` structure name itself — so nothing needs
appending anymore. This walk is kept as the executable statement of what the recovery must find,
with its completeness proof in `Proofs/Deps.lean`; a `#guard` in `Test/Deps.lean` pins core's new
behavior, and if core ever drops the name again, restoring `++ projStructureNames e` in
`exprUsedConstants` is the fix.

This was a correctness guard, not a fix for an observed failure. Surface-level field access
(`x.field`) elaborates to an application of the projection *function* (`S.field x`), which
`getUsedConstants` reports normally; bare `.proj` nodes come from the compiler's own recursion
machinery (`brecOn`, `._f`, `.wf._unary._proof_n`) and from upstream `Equiv`/`Subtype`-style
bundled structures. Scanning the 438950-constant environment of a Mathlib-backed target found 14
distinct names lost this way — `PProd`, `WellFoundedRelation`, `Equiv`, `Subtype`, `Zero`, ... —
and **none** of them was a declaration of the target project itself. Such names are dropped
anyway by consumers that keep only the project's own declarations, so recovering them changes no
output today; they are simply the correct input to those filters if a project ever does elaborate
a `.proj` of one of its own structures.

The walk memoizes on the `Expr` nodes themselves so heavily-shared proof terms are not re-walked:
`Hashable Expr` is the hash cached in the expression header and `BEq Expr` is the native
`Expr.eqv`, so both are cheap. It is still ~3x the cost of core's `foldConsts` (which memoizes on
a pointer set from unsafe code); that is immaterial here because only the target project's own
constants are ever walked. -/
def projStructureNames (e : Expr) : Array Name :=
  (go e (#[], {})).1
where
  -- `e` is memoized *after* its subterms are walked, not before. Either order computes the same
  -- thing — a term is never a strict subterm of itself, so a node being walked can never be
  -- re-encountered inside its own walk — but marking it afterwards means the memo satisfies a
  -- simple invariant throughout: everything in `seen` has already contributed its names to `acc`.
  -- That is what `Proofs/Deps.lean` inducts on to show the memo loses nothing.
  go (e : Expr) (st : Array Name × Std.HashSet Expr) : Array Name × Std.HashSet Expr :=
    let (acc, seen) := st
    if seen.contains e then
      st
    else
      let (acc, seen) :=
        match e with
        | .app f a => go a (go f (acc, seen))
        | .lam _ t b _ => go b (go t (acc, seen))
        | .forallE _ t b _ => go b (go t (acc, seen))
        | .letE _ t v b _ => go b (go v (go t (acc, seen)))
        | .mdata _ b => go b (acc, seen)
        | .proj s _ b => go b (acc.push s, seen)
        | _ => (acc, seen)
      (acc, seen.insert e)

/-- The constants used by `e`, including the structure name of every `Expr.proj` node.

Since Lean 4.34 this is `Expr.getUsedConstants` unchanged — core's `foldConsts` now visits the
`.proj` structure name itself, closing the gap `projStructureNames` was appended here to cover
(see its docstring). The wrapper stays as the named seam every dependency computation goes
through: if core ever drops the name again — the `#guard`s in `Test/Deps.lean` would catch it —
the fix is `e.getUsedConstants ++ projStructureNames e` here, and nowhere else. -/
def exprUsedConstants (e : Expr) : Array Name :=
  e.getUsedConstants

/-- One-level "used constants" for a declaration's type (and, if `includeValue`, also its
value/body), handling inductive constructor types and structure field-default functions: for
inductives/structures, `info.type` alone does not mention constructor field types, so those are
pulled in from the constructors' types and (for structures) field-default functions. -/
def usedConstantsOf (env : Environment) (name : Name) (info : ConstantInfo)
    (includeValue : Bool) : Array Name :=
  let typeUsed :=
    match info with
    | .inductInfo val =>
      val.ctors.foldl (fun acc ctorName =>
        match env.find? ctorName with
        | some ctorInfo => acc ++ exprUsedConstants ctorInfo.type
        | none => acc) (exprUsedConstants info.type)
    | _ => exprUsedConstants info.type
  if !includeValue then
    typeUsed
  else
    let valueUsed :=
      match info with
      | .defnInfo val => exprUsedConstants val.value
      | .thmInfo val => exprUsedConstants val.value
      | .inductInfo _ =>
        if (getStructureInfo? env name).isNone then
          #[]
        else
          (getStructureFields env name).foldl (fun acc fieldName =>
            match getDefaultFnForField? env name fieldName with
            | some defaultFn =>
              match env.find? defaultFn >>= ConstantInfo.value? with
              | some value => acc ++ exprUsedConstants value
              | none => acc
            | none => acc) #[]
      | _ => #[]
    typeUsed ++ valueUsed

/-! ## Data dependencies: a value's meaning, minus the proofs inside it

A bundled structure instance carries data fields *and* proof obligations:

```lean
noncomputable def SquareIntegrable.toL2Isom : SquareIntegrable ι E P 𝓕 ≃ₗᵢ[ℝ] lpMeas … where
  toFun X := ⟨toL2 ι E P 𝓕 X, by …⟩
  invFun X := …
  left_inv X := by …
  right_inv X := by …
```

`left_inv` and `right_inv` are proofs, kernel-checked exactly as a theorem's proof is. By the
argument that an upstream proof needs no trust — the kernel rechecked it, and anything left
unproved arrives as a `sorry` or an extra axiom — they say nothing about what the definition
*means*. Yet `usedConstantsOf … (includeValue := true)` reports every
lemma their tactics happened to call: on the declaration above that is the difference between 132
dependencies and 280, and it is what puts definitions at the top of every degree distribution while
`structure`, `inductive` and `typeclass` (whose value contributions are field types and defaults,
never proofs) show no excess at all.

The walk below is `exprUsedConstants` with one change: at an application that *returns a structure or
class*, it skips the arguments filling that constant's `Prop`-valued parameters (`constPropMask`).
It recurses, so a proof nested inside a data field is skipped too — the `by` block above is the
second field of a `Subtype.mk` sitting inside `toFun`, and is reached by exactly the same rule.

The restriction to structure-returning applications is what keeps the rule true. "The `Prop`
arguments of an application that returns a structure are that instance's obligations" is a fact
about bundled structures; "every `Prop` argument is an obligation" is not, and the case it gets
wrong is choice. `noncomputable def IsPreBrownianReal.mk X h := h.exists_continuous_modification.choose`
elaborates to `Exists.choose _ p (IsPreBrownianReal.exists_continuous_modification h)`, whose third
parameter is a proof — so an unrestricted mask dropped the *only* project declaration in the body,
and the site reported that definition as resting on nothing. `Exists.choose` returns a bare type
variable, not a structure, so the restriction keeps it. See `constPropMask` for what this costs.

The mask is read off *declared types*, not inferred from the arguments, which is what keeps it cheap
and context-free: nothing here has to type-check a subterm sitting under binders.

This is deliberately *not* applied to a theorem's own proof. A caller that wants a theorem's
statement alone already drops that wholesale by taking `typeDeps`, and the two mechanisms are kept
separate so that neither has to be correct about the other's case.
-/

/-- For each parameter position of the constant `fn`, whether that parameter is `Prop`-valued, i.e.
filled by a proof rather than by data — but only when `fn` *returns* a structure or class, since
that is the case in which its `Prop` parameters really are a bundled instance's obligations. Every
other constant masks nothing.

Read off `fn`'s *declared type*, which makes this both cheap and independent of any local context:
telescoping `∀ (x₁ : T₁) … (xₙ : Tₙ), R` binds each parameter as a local hypothesis, so `isProof`
can ask a well-posed question about it even when the argument at that position, in the term being
walked, sits under binders of its own, and leaves `R`'s head constant in hand for the structure test.

Keyed on the *return type*, not on `fn` being a constructor. A structure instance is very often
built by *calling* something that returns the structure rather than by a constructor literal —
`instance : NormedAddCommGroup … := Function.Injective.normedAddCommGroup hf hproof …` — and the
proof obligations are then ordinary arguments to an ordinary function. Masking constructors alone
left 188 of `BrownianMotion`'s 263 non-theorem declarations completely unreduced, all of this shape;
keying on the return type covers them, because `NormedAddCommGroup β` is a class.

What the restriction costs, measured over `BrownianMotion`'s 232 exposed definitions: the value walk
reports 9654 edges unmasked and 6476 with a mask over *every* `Prop` parameter, so the mask removes
3178; restricted to structure-returning applications it removes 2985 of those 3178, and the count of
declarations it reduces not at all goes from 97 to 130. Nearly all of the difference is Prop-valued
*typeclass instances* (`[IsProbabilityMeasure P]` and friends) on type formers such as
`SimpleProcess` and `ClassD`, whose result is a `Sort` rather than a structure application.

The head constant is taken as written, without `whnf`: a `def F : Type _ := ↥someSubmodule` masks
nothing even though it unfolds to a `Subtype`. That is the conservative direction, and it avoids
reducing an arbitrary return type. Note one case the rule does not catch:
`Classical.indefiniteDescription` returns `{x // p x}`, a `Subtype`, so its proof argument is still
masked — `Classical.choose`, `Exists.choose` and `Nonempty.some` all return a bare type variable and
are not.

Returns `#[]` — every position data — when `fn` is unknown, does not return a structure, or its type
will not telescope. That is the conservative direction: it can only keep edges a correct mask would
have dropped, never drop one it would have kept. -/
def constPropMask (fn : Name) : MetaM (Array Bool) := do
  let env ← getEnv
  let some info := env.find? fn | return #[]
  try
    Meta.forallTelescopeReducing info.type fun xs body => do
      let some head := body.getAppFn.constName? | return #[]
      unless isStructure env head do return #[]
      xs.mapM Meta.isProof
  catch _ =>
    return #[]

/-- Walk state for `dataValueConstants`: the memo over already-visited nodes (same rationale as
`projStructureNames` — heavily shared proof terms must not be re-walked), the constructor masks
computed so far (shared across declarations, since `Meta.forallTelescopeReducing` on a Mathlib
structure is far from free), and the constants collected. -/
private structure DataWalk where
  seen : Std.HashSet Expr := {}
  masks : Std.HashMap Name (Array Bool) := {}
  acc : Array Name := #[]

private partial def dataWalkGo (e : Expr) : StateT DataWalk MetaM Unit := do
  if (← get).seen.contains e then
    return
  modify fun s => { s with seen := s.seen.insert e }
  -- An application of a named constant is where the mask applies. Handled before the structural
  -- match and returning early, so the spine's partial applications are never walked generically —
  -- which is what makes skipping a proof argument actually skip it.
  if e.isApp then
    if let .const c _ := e.getAppFn then
      let mask ← match (← get).masks.get? c with
        | some m => pure m
        | none =>
          let m ← constPropMask c
          modify fun s => { s with masks := s.masks.insert c m }
          pure m
      modify fun s => { s with acc := s.acc.push c }
      let args := e.getAppArgs
      for h : i in [0:args.size] do
        -- `none` (over-application past the declared telescope) counts as data.
        if mask[i]? != some true then
          dataWalkGo args[i]
      return
  match e with
  | .app f a => dataWalkGo f; dataWalkGo a
  | .lam _ t b _ => dataWalkGo t; dataWalkGo b
  | .forallE _ t b _ => dataWalkGo t; dataWalkGo b
  | .letE _ t v b _ => dataWalkGo t; dataWalkGo v; dataWalkGo b
  | .mdata _ b => dataWalkGo b
  -- Same recovery as `projStructureNames`: the structure name of a `.proj` is otherwise lost.
  | .proj s _ b => modify fun st => { st with acc := st.acc.push s }; dataWalkGo b
  | .const c _ => modify fun st => { st with acc := st.acc.push c }
  | _ => pure ()

/-- The constants a declaration's *value* mentions outside the proofs inside it, or `#[]` when it
has no value this applies to.

Only `.defnInfo` — `def`, `abbrev` and `instance`, the kinds that can carry a bundled structure
instance. A theorem's value is handled by the caller taking `typeDeps` instead, and
`structure`/`inductive` contribute field types and defaults rather than a value, with no proof
excess to remove.

Not `@[expose]`, for the same reason as `evalNameExpr?`: the body refers to the `private`
`dataWalkGo`. Nothing is lost, since no importer needs to unfold this. -/
@[no_expose] def dataValueConstants (info : ConstantInfo) : MetaM (Array Name) := do
  match info with
  | .defnInfo val =>
    let (_, st) ← (dataWalkGo val.value).run {}
    return st.acc
  | _ => return #[]

/-- `dataValueConstants` of each of `infos`, sharing the parameter masks (`constPropMask`) between
them: many declarations apply the same constants, and a mask costs a telescope of the constant's
type. -/
@[no_expose] def dataValueConstantsOf (infos : Array ConstantInfo) : MetaM (Array (Array Name)) := do
  let mut masks : Std.HashMap Name (Array Bool) := {}
  let mut out := #[]
  for info in infos do
    match info with
    | .defnInfo val =>
      let (_, st) ← (dataWalkGo val.value).run { masks }
      masks := st.masks
      out := out.push st.acc
    | _ => out := out.push #[]
  return out

/-! ## Dependencies the elaborated term does not mention: notation -/

/-- The `String` a string-literal `Expr` holds, if `e` is one. -/
private def exprStrLit? (e : Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- Reconstructs the `Name` value that `e` builds, if `e` is a `Name.anonymous`/`Name.str`/
`Name.mkStr1..4` application. Notation and macro definitions store the constants they expand to as
pre-resolved `Name` *data* built this way (inside the embedded `Syntax`), so these references are
invisible to `Expr.getUsedConstants`; reconstructing them is how we recover the dependency.

Not `@[expose]`, so that the body may keep referring to the `private` `exprStrLit?`. Nothing is
lost: this is a `partial` definition, so importers cannot unfold it either way. -/
@[no_expose] partial def evalNameExpr? (e : Expr) : Option Name := do
  match e.getAppFnArgs with
  | (``Lean.Name.anonymous, _) => some .anonymous
  | (``Lean.Name.mkStr1, #[a]) => some (.str .anonymous (← exprStrLit? a))
  | (``Lean.Name.mkStr2, #[a, b]) =>
    some (.str (.str .anonymous (← exprStrLit? a)) (← exprStrLit? b))
  | (``Lean.Name.mkStr3, #[a, b, c]) =>
    some (.str (.str (.str .anonymous (← exprStrLit? a)) (← exprStrLit? b)) (← exprStrLit? c))
  | (``Lean.Name.mkStr4, #[a, b, c, d]) =>
    some (.str (.str (.str (.str .anonymous (← exprStrLit? a)) (← exprStrLit? b)) (← exprStrLit? c))
      (← exprStrLit? d))
  | (``Lean.Name.str, #[p, s]) => some (.str (← evalNameExpr? p) (← exprStrLit? s))
  | _ => none

/-- Every `Name` value embedded anywhere in `e` (reconstructed via `evalNameExpr?`), in pre-order.

The walk memoizes on the `Expr` nodes, as `projStructureNames` does: a subterm shared by several
parents is walked once. A plain tree walk visits a shared subterm once per path to it, which is
exponential in the depth of sharing, and the values of large definitions share a great deal (on Tau
Ceti, one such value kept `notationExpansionDeps` busy for more than 18 minutes). Skipping a
subterm already walked only drops repetitions of names already collected, so the names come out in
the same order of first occurrence as a tree walk would give, each at most as often. -/
def collectEmbeddedNames (e : Expr) : Array Name :=
  (go e (#[], {})).1
where
  go (e : Expr) (st : Array Name × Std.HashSet Expr) : Array Name × Std.HashSet Expr :=
    let (acc, seen) := st
    if seen.contains e then
      st
    else
      let acc := match evalNameExpr? e with
        | some n => acc.push n
        | none => acc
      let (acc, seen) :=
        match e with
        | .app f a => go a (go f (acc, seen))
        | .lam _ t b _ => go b (go t (acc, seen))
        | .forallE _ t b _ => go b (go t (acc, seen))
        | .letE _ t v b _ => go b (go v (go t (acc, seen)))
        | .mdata _ b => go b (acc, seen)
        | .proj _ _ b => go b (acc, seen)
        | _ => (acc, seen)
      (acc, seen.insert e)

/-- The constants from which `evalNameExpr?` reconstructs a `Name`. -/
def nameBuilders : Array Name :=
  #[``Lean.Name.anonymous, ``Lean.Name.str, ``Lean.Name.mkStr1, ``Lean.Name.mkStr2,
    ``Lean.Name.mkStr3, ``Lean.Name.mkStr4]

/-- Whether `e` mentions one of `nameBuilders`, that is, whether it can embed a `Name` at all.
`Expr.find?` visits each shared subterm once, so this is cheap even on large values. -/
def buildsName (e : Expr) : Bool :=
  (e.find? fun
    | .const n _ => nameBuilders.contains n
    | _ => false).isSome

/-- True if `n` names a notation/syntax parser (its type is `Lean.ParserDescr`/`TrailingParserDescr`). -/
def isNotationKind (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some info => info.type.isConstOf ``Lean.ParserDescr || info.type.isConstOf ``Lean.TrailingParserDescr
  | none => false

/-- Maps each notation parser to the constants its expansion references. A notation's macro definition
embeds both its own parser kind and the constant(s) it abbreviates as pre-resolved `Name` data (see
`evalNameExpr?`). Scanning the project's definitions, any whose body embeds a notation kind `K`
contributes its other embedded (real) constants as dependencies of `K` — so a standalone rendering
of `K` inlines what it stands for instead of failing with `unknown constant`. -/
def notationExpansionDeps (env : Environment) (projectConsts : Array (Name × Name × ConstantInfo)) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for (_, _, cinfo) in projectConsts do
    if let .defnInfo v := cinfo then
      -- Most values build no `Name`, and so embed none: `buildsName` rules them out cheaply.
      unless buildsName v.value do continue
      let names := (collectEmbeddedNames v.value).filter (env.contains ·)
      let kinds := names.filter (isNotationKind env ·)
      unless kinds.isEmpty do
        let realDeps := names.filter (!isNotationKind env ·)
        for k in kinds do
          m := m.insert k ((m.getD k #[]) ++ realDeps)
  return m

/-! ## Dependencies the elaborated term does not mention: coercions -/

/-- Coercion type classes whose instances Lean unfolds at use sites: an elaborated term keeps only
the underlying `@[coe]` function, never the instance, so a coercion's dependency on its instance is
invisible to `getUsedConstants`. The instance must still be replayed for the source's `↑`/`⇑` to
elaborate. -/
def coercionClasses : List Name :=
  [``CoeFun, ``CoeSort, ``Coe, ``CoeTC, ``CoeHead, ``CoeTail, ``CoeHTCT, ``CoeOut, ``CoeDep]

/-- If `type` is, under its binders, a coercion-class application `Cls Src …`, the type coerced
*from* (`Src`). -/
def coercionSource? (type : Expr) : Option Expr :=
  match type with
  | .forallE _ _ b _ => coercionSource? b
  | _ =>
    let (fn, args) := type.getAppFnArgs
    if coercionClasses.contains fn && args.size ≥ 1 then some args[0]!
    else none

/-- If `type` is, under its binders, a coercion-class application `Cls Src …`, the head constant of
`Src`. -/
def coercionSourceType? (type : Expr) : Option Name :=
  coercionSource? type >>= (·.getAppFn.constName?)

/-- A coercion instance, together with the project constants that must be present for it to be
relevant (see `coercionInstancesByType`). -/
structure CoercionInstance where
  /-- The instance declaration. -/
  name : Name
  /-- Project-local constants occurring in the coerced-from type, other than its head. -/
  witnesses : Array Name
deriving Inhabited

/-- Maps a type's head constant to the exposed coercion instances coercing *from* it. A declaration
mentioning such a type needs these instances replayed so its source coercions still elaborate (the
instances themselves never appear in the elaborated term; see `coercionClasses`).

The head constant alone is too coarse a key. `instance : CoeFun (SquareIntegrable ι E P 𝓕) …` has
coerced-from type `{ x // x ∈ SquareIntegrable … }`, whose head is **`Subtype`** — so keying on the
head filed it under `Subtype` and handed it to every declaration mentioning a subtype at all. In
brownian-motion that was 208 declarations, none of which mention `SquareIntegrable`, and each one
inherited `SquareIntegrable`'s whole closure. Many of those declarations live in modules that do
not even import the one defining the instance, so the edge was not merely useless but impossible.

`witnesses` records the other project constants in the coerced-from type (`SquareIntegrable` here),
and `Context.declDeps` only replays the instance for declarations that mention all of them. -/
def coercionInstancesByType (env : Environment) (rootPrefix : Name) (exposed : Std.HashSet Name)
    (projectConsts : Array (Name × Name × ConstantInfo)) :
    Std.HashMap Name (Array CoercionInstance) := Id.run do
  let mut m : Std.HashMap Name (Array CoercionInstance) := {}
  for (cname, _, cinfo) in projectConsts do
    if exposed.contains cname && Lean.Meta.isInstanceCore env cname then
      if let some src := coercionSource? cinfo.type then
        if let some head := src.getAppFn.constName? then
          let witnesses := src.getUsedConstants.filter fun c =>
            c != head && isProjectLocalConst env rootPrefix c
          m := m.insert head ((m.getD head #[]).push { name := cname, witnesses })
  return m

/-! ## Expansion through compiler-generated helpers -/

/-- Memo table for the one-level expansion of internal helpers, shared across the declarations of
one run (see `expandThroughInternals`). -/
abbrev Cache := Std.HashMap Name (Array Name)

/-- Expands `start` by looking through every constant `isHelper` accepts: such a constant is
replaced by what it uses (`usedConstantsOf`, value included), recursively, and every other constant
is kept as it is. `cache` memoizes the one-level expansion of helpers across calls.

This mirrors the recursive dependency-collection idea from
https://github.com/mattrobball/lean-informal/blob/main/Informal/Deps.lean. -/
partial def expandThrough (env : Environment) (isHelper : Name → Bool) (cache : Cache)
    (start : Array Name) : Array Name × Cache :=
  go cache {} #[] start.toList
where
  go (cache : Cache) (visited : Std.HashSet Name) (acc : Array Name) :
      List Name → Array Name × Cache
    | [] => (acc, cache)
    | n :: rest =>
      if visited.contains n then
        go cache visited acc rest
      else
        let visited := visited.insert n
        if !isHelper n then
          go cache visited (acc.push n) rest
        else
          match cache.get? n with
          | some deps => go cache visited acc (rest ++ deps.toList)
          | none =>
            match env.find? n with
            | none => go cache visited acc rest
            | some info =>
              let deps := usedConstantsOf env n info true
              go (cache.insert n deps) visited acc (rest ++ deps.toList)

/-- Expands `start` by following constants that are project-local (share `rootPrefix`) but are
not themselves exposed declarations — i.e. compiler-generated helpers such as `_proof_N`,
`match_..`, or structure field-default functions — recursively pulling in whatever *they* depend
on instead of stopping at their (uninformative) name. Exposed declarations and external
(non-project) constants are kept as-is without further expansion: `expandThrough` with the project
boundary, which is what `Context.declDeps` does under the default `Options`. -/
def expandThroughInternals (env : Environment) (rootPrefix : Name)
    (exposed : Std.HashSet Name) (cache : Cache) (start : Array Name) : Array Name × Cache :=
  expandThrough env (fun n => !exposed.contains n && isProjectLocalConst env rootPrefix n) cache start

/-! ## Per-declaration dependencies -/

/-- The dependencies of one declaration. -/
structure DeclDeps where
  /-- Constants used by the declaration's *type*, expanded through compiler-generated helpers and
  deduplicated. Never contains the declaration itself. -/
  typeDeps : Array Name
  /-- Constants used by the declaration's type *and* its value/body (plus, for a notation, what its
  expansion references), expanded and deduplicated the same way. Never contains the declaration
  itself. -/
  deps : Array Name
  /-- Like `deps`, but with the proofs inside the value skipped (`dataValueConstants`): what the
  declaration's statement and *data* rest on, dropping the lemmas its embedded proof obligations
  happen to call.

  Equal to `deps` unless the `Context` was built with `withDataValueConsts` *and* this declaration
  is a `.defnInfo`, so a caller that does not ask for the extra analysis sees no change. -/
  dataDeps : Array Name
deriving Repr, Inhabited

/-- Which of `DeclDeps`' lists to compute. A list not asked for is left empty.

`deps` is most of the cost: it walks the whole value, every proof term included, while `typeDeps`
walks the statement and `dataDeps` skips the proofs inside a value when the `Context` has data values
for it. A caller that only needs what declarations *mean* asks for `{ deps := false }`. -/
structure DepsRequest where
  /-- Compute `DeclDeps.deps`. -/
  deps : Bool := true
  /-- Compute `DeclDeps.dataDeps`. For a declaration without a data value in the `Context` (a
  theorem, or any declaration when `withDataValueConsts` was not run), `dataDeps` is `deps`, and so
  walks the whole value even when `deps` itself is not asked for. -/
  dataDeps : Bool := true
deriving Repr, Inhabited

/-- The project-wide tables the per-declaration analysis needs, computed once by `Context.of` and
reused for every declaration. -/
structure Context where
  env : Environment
  /-- Where the analysis stops, and which constants are declarations. -/
  options : Options := {}
  /-- Root module prefix delimiting the project: a constant counts as project-local when the module
  declaring it has this prefix (see `isProjectLocalConst`). -/
  rootPrefix : Name
  /-- Every constant declared by a project module, as `(name, module, info)`. -/
  constants : Array (Name × Name × ConstantInfo)
  /-- The project's declarations, under `options.display` (by default those a person wrote:
  `shouldExpose`); expansion stops at these. -/
  exposed : Std.HashSet Name
  /-- Notation kind ↦ constants its expansion references (`notationExpansionDeps`). -/
  notationDeps : Std.HashMap Name (Array Name)
  /-- Type head constant ↦ coercion instances coercing from it (`coercionInstancesByType`). -/
  coercionInstances : Std.HashMap Name (Array CoercionInstance)
  /-- Project constant ↦ the module declaring it. -/
  declModule : Std.HashMap Name Name
  /-- Project module ↦ the project modules it can see (`visibleProjectModules`). -/
  visibleModules : Std.HashMap Name (Std.HashSet Name)
  /-- Declaration ↦ the constants its value mentions outside its proofs (`dataValueConstants`).

  Empty unless `withDataValueConsts` has been run, and populated only for `.defnInfo`; `declDeps`
  falls back to the full value walk for anything absent, so `DeclDeps.dataDeps` degrades to `deps`
  rather than to nothing. Filling it needs `MetaM` (deciding whether a constructor field is
  `Prop`-valued is a typing question), which is why it is a separate pass rather than part of the
  pure `Context.of`. -/
  dataValueConsts : Std.HashMap Name (Array Name) := {}

/-- For each project module, the project modules it can see: itself plus everything it imports,
transitively.

Only project modules are tracked. A project module can only be reached from another project module
(nothing upstream imports the project), so reachability among them never leaves the set.

Relies on `moduleNames` being in dependency order — Lean writes a module's imports before the
module itself — so one forward pass suffices. -/
def visibleProjectModules (env : Environment) (rootPrefix : Name) :
    Std.HashMap Name (Std.HashSet Name) := Id.run do
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut visible : Std.HashMap Name (Std.HashSet Name) := {}
  for i in [0:names.size] do
    let modName := names[i]!
    if !hasPrefixName modName rootPrefix then
      continue
    let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert modName
    if h : i < data.size then
      for imp in data[i].imports do
        if hasPrefixName imp.module rootPrefix then
          seen := seen.insert imp.module
          for m in visible.getD imp.module {} do
            seen := seen.insert m
    visible := visible.insert modName seen
  return visible

/-- Scans `env` for the project rooted at `rootPrefix` and builds the tables `Context.declDeps`
needs. Does the whole-environment work once, so a caller analysing many declarations should build
this a single time.

The tables are the project's under any `options`: notation and coercion instances are recovered for
the project's own declarations, whose source is what they serve, and with `Boundary.none` an
upstream declaration is analysed from its elaborated term alone. -/
def Context.of (env : Environment) (rootPrefix : Name) (options : Options := {}) : Context :=
  let constants := projectConstants env rootPrefix
  let exposed : Std.HashSet Name :=
    constants.foldl (fun acc (name, _, info) =>
      if options.display.accepts env name info then acc.insert name else acc) {}
  { env := env
    options := options
    rootPrefix := rootPrefix
    constants := constants
    exposed := exposed
    notationDeps := notationExpansionDeps env constants
    coercionInstances := coercionInstancesByType env rootPrefix exposed constants
    declModule := constants.foldl (fun acc (name, mod, _) => acc.insert name mod) {}
    visibleModules := visibleProjectModules env rootPrefix }

/-- Whether expansion stops at `n`, which is then a node of the graph, rather than looking through
it. A project constant is a node when it is one of the project's declarations (`exposed`). Past the
project, under `Boundary.project` every constant is a leaf, and under `Boundary.none` a constant is a
node when it is a declaration under `options.display`, and is looked through otherwise. -/
def Context.stopsAt (ctx : Context) (n : Name) : Bool :=
  if ctx.declModule.contains n then
    ctx.exposed.contains n
  else match ctx.options.boundary with
    | .project => true
    | .none =>
      match ctx.env.find? n with
      | some info => ctx.options.display.accepts ctx.env n info
      | none => true

/-- The dependencies of the single declaration `name` (whose `ConstantInfo` is `info`), threading
the memo `cache` used by `expandThrough`; the updated cache is returned alongside and
should be passed to the next call. `request` says which lists to compute (all by default).

`name` is normally one of the project's declarations. Under `Boundary.none` it can be any
declaration of the environment. -/
def Context.declDeps (ctx : Context) (cache : Cache) (name : Name) (info : ConstantInfo)
    (request : DepsRequest := {}) : DeclDeps × Cache :=
  -- Adds, for every referenced type with coercion instances, those instances (see `coercionClasses`),
  -- but only the ones whose coerced-from type this declaration actually mentions in full: the head
  -- constant on its own is far too coarse a match (see `coercionInstancesByType`).
  let addCoercionInsts (cs : Array Name) : Array Name :=
    let present : Std.HashSet Name := cs.foldl (fun acc c => acc.insert c) {}
    cs ++ cs.foldl (init := #[]) fun acc c =>
      acc ++ (ctx.coercionInstances.getD c #[]).filterMap fun inst =>
        if inst.witnesses.all present.contains then some inst.name else none
  let typeUsedConstants := addCoercionInsts (usedConstantsOf ctx.env name info false)
  -- When this declaration *is* a notation, also depend on the constants it expands to (which are
  -- stored as `Name` data inside its macro and so invisible to `getUsedConstants`); see
  -- `notationExpansionDeps`. The reverse direction (a declaration whose *source* uses a notation)
  -- is syntactic, and so is left to callers that have the source syntax at hand.
  -- The value walk, proofs included, only when a requested list needs it: for a theorem it is the
  -- whole proof term, most of the cost of the analysis.
  let dataValue? := ctx.dataValueConsts.get? name
  let needAll := request.deps || (request.dataDeps && dataValue?.isNone)
  let allUsedConstants :=
    if needAll then
      addCoercionInsts (usedConstantsOf ctx.env name info true ++ ctx.notationDeps.getD name #[])
    else #[]
  -- The same inputs as `allUsedConstants`, with the value's contribution replaced by its
  -- proof-skipped form where one was computed. Everything downstream — coercion instances,
  -- expansion through internal helpers, the visibility filter — is applied identically, so the
  -- result is comparable to `deps` edge for edge.
  let dataUsedConstants :=
    match dataValue? with
    | some valueConsts =>
      if request.dataDeps then
        addCoercionInsts (usedConstantsOf ctx.env name info false ++ valueConsts
          ++ ctx.notationDeps.getD name #[])
      else #[]
    | none => allUsedConstants
  let expand (cache : Cache) (wanted : Bool) (cs : Array Name) : Array Name × Cache :=
    if wanted then expandThrough ctx.env (!ctx.stopsAt ·) cache cs
    else (#[], cache)
  let (typeExpanded, cache) := expand cache true typeUsedConstants
  let (allExpanded, cache) := expand cache request.deps allUsedConstants
  let (dataExpanded, cache) := expand cache request.dataDeps dataUsedConstants
  -- A declaration can only reference what its own module can see. Any project-local dependency in
  -- a module this one does not import is impossible, so it is an artifact of the analysis (a
  -- too-eagerly replayed coercion instance, say) rather than a real edge. Constants outside the
  -- project are left alone: they are never emitted, and pruning them here would only hide them
  -- from the assumption counts.
  let visible := ctx.visibleModules.getD (ctx.declModule.getD name .anonymous) {}
  let importable (dep : Name) : Bool :=
    match ctx.declModule.get? dep with
    | none => true
    | some mod => visible.contains mod
  -- First occurrences, in order. A hash set rather than `Array.contains`, which made this quadratic
  -- in the length of the list.
  let dedup (cs : Array Name) : Array Name := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut out := #[]
    for dep in cs do
      if dep == name || seen.contains dep then continue
      seen := seen.insert dep
      if importable dep then out := out.push dep
    return out
  ({ typeDeps := dedup typeExpanded, deps := dedup allExpanded, dataDeps := dedup dataExpanded },
    cache)

/-- Fills `Context.dataValueConsts` for every exposed `.defnInfo`, so that `declDeps` can report
`DeclDeps.dataDeps`; with `only`, for those of them in `only`.

Restricted to `.defnInfo` because that is where the excess is: `def` and `instance` account for
essentially all of the gap between `typeDeps` and `deps` (on `BrownianMotion`, 6709 of 6711 edges),
while `structure`, `inductive` and `typeclass` show none. That also keeps the cost proportional to a
small minority of declarations — 263 of 1692 there — rather than to the whole project. -/
def Context.withDataValueConsts (ctx : Context) (only : Option (Std.HashSet Name) := none) :
    MetaM Context := do
  let mut consts : Std.HashMap Name (Array Name) := {}
  for (name, _, info) in ctx.constants do
    if ctx.exposed.contains name && only.all (·.contains name) then
      if info matches .defnInfo _ then
        consts := consts.insert name (← dataValueConstants info)
  return { ctx with dataValueConsts := consts }

/-- Adds to `Context.dataValueConsts` the data values of those of `names` that are definitions and
have none yet, wherever they come from: what `Context.closure` needs past the project. -/
def Context.withDataValuesFor (ctx : Context) (names : Array Name) : MetaM Context := do
  let todo := names.filterMap fun n =>
    if ctx.dataValueConsts.contains n then none
    else match ctx.env.find? n with
      | some info@(.defnInfo _) => some (n, info)
      | _ => none
  let values ← dataValueConstantsOf (todo.map (·.2))
  let consts := (todo.zip values).foldl (fun m ((n, _), v) => m.insert n v) ctx.dataValueConsts
  return { ctx with dataValueConsts := consts }

/-- The dependencies of each of `targets`, in the order of `targets`: the same as calling
`declDeps` on each in turn, but in parallel. The targets are split into chunks of `chunk`
declarations, each processed by its own task with its own expansion cache; the cache is only a memo,
so the result does not depend on the chunking. -/
def Context.depsOf (ctx : Context) (targets : Array (Name × ConstantInfo))
    (request : DepsRequest := {}) (chunk : Nat := 256) : Array (Name × DeclDeps) :=
  let chunk := max chunk 1
  let tasks := (Array.range ((targets.size + chunk - 1) / chunk)).map fun i =>
    let part := targets.extract (i * chunk) ((i + 1) * chunk)
    Task.spawn fun _ => Id.run do
      let mut cache : Cache := {}
      let mut out : Array (Name × DeclDeps) := #[]
      for (name, info) in part do
        let (deps, cache') := ctx.declDeps cache name info request
        cache := cache'
        out := out.push (name, deps)
      return out
  tasks.foldl (fun acc t => acc ++ t.get) #[]

/-- The dependencies of every exposed declaration of the project, in environment order
(`Context.depsOf`, in parallel). -/
def Context.allDeclDeps (ctx : Context) (request : DepsRequest := {}) : Array (Name × DeclDeps) :=
  ctx.depsOf (ctx.constants.filterMap fun (name, _, info) =>
    if ctx.exposed.contains name then some (name, info) else none) request

/-! ## Where a dependency comes from -/

/-- What made `declDeps` report a dependency. -/
inductive Source where
  /-- It occurs in the declaration's type. -/
  | type
  /-- It occurs in the declaration's value, outside the proofs the data walk skips (for `dataDeps`),
  or anywhere in the value (for `deps`). -/
  | value
  /-- It occurs in the type or value of a helper that was looked through: `chain` is the helpers
  from the declaration to the one that mentions it, and `proofs` says which of them are proofs
  (theorems, such as the `_proof_N` Lean lifts out of a definition). -/
  | helper (chain : List Name) (proofs : List Bool)
  /-- It is a coercion instance, replayed because the declaration mentions the type it coerces from. -/
  | coercion
  /-- It is a constant the declaration's notation expands to. -/
  | notation
deriving Repr, BEq, Inhabited

/-- Every source of the dependency of `name` on `target` in `DeclDeps.dataDeps` (`data := true`) or
`DeclDeps.deps` (`data := false`), as `declDeps` computes them: an empty array when there is no such
dependency. For a helper chain, the shortest one. Uses the context's data values when it has them. -/
def Context.sources (ctx : Context) (name : Name) (info : ConstantInfo) (target : Name)
    (data : Bool := true) : Array Source := Id.run do
  let env := ctx.env
  let typeUsed := usedConstantsOf env name info false
  let valueUsed :=
    match ctx.dataValueConsts.get? name with
    | some v => if data then v else (usedConstantsOf env name info true)
    | none => usedConstantsOf env name info true
  let notationUsed := ctx.notationDeps.getD name #[]
  let present : Std.HashSet Name := (typeUsed ++ valueUsed).foldl (·.insert ·) {}
  let coercions := (typeUsed ++ valueUsed).foldl (init := #[]) fun acc c =>
    acc ++ (ctx.coercionInstances.getD c #[]).filterMap fun inst =>
      if inst.witnesses.all present.contains then some inst.name else none
  let mut out := #[]
  if typeUsed.contains target then out := out.push .type
  if valueUsed.contains target && !typeUsed.contains target then out := out.push .value
  if coercions.contains target then out := out.push .coercion
  if notationUsed.contains target then out := out.push .notation
  -- Looking through helpers, breadth-first, as `expandThrough` does, remembering how each helper
  -- was reached.
  let seeds := (typeUsed ++ valueUsed ++ coercions ++ notationUsed).filter (!ctx.stopsAt ·)
  let mut parent : Std.HashMap Name Name := {}
  let mut queue : Array Name := #[]
  for h in seeds do
    unless parent.contains h do
      parent := parent.insert h name
      queue := queue.push h
  let mut k := 0
  let mut found := false
  while k < queue.size && !found do
    let h := queue[k]!
    k := k + 1
    let some hi := env.find? h | continue
    let used := usedConstantsOf env h hi true
    if used.contains target then
      let mut chain := [h]
      let mut cur := h
      while parent.getD cur name != name do
        cur := parent.getD cur name
        chain := cur :: chain
      let proofs := chain.map fun c => (env.find? c).any (·.isTheorem)
      out := out.push (.helper chain proofs)
      found := true
    for c in used do
      if !ctx.stopsAt c && !parent.contains c then
        parent := parent.insert c h
        queue := queue.push c
  return out

/-! ## Closures past the project -/

/-- What `Context.closure` follows out of a declaration it reaches. A proof contributes its
statement under every rule: what a theorem rests on is what it states, not what its proof happened
to call. -/
inductive Follow where
  /-- Statements only (`typeDeps`). -/
  | statement
  /-- What declarations mean: a definition's statement and the data of its value, the proofs
  inside it skipped (`dataDeps`). -/
  | meaning
  /-- Everything a definition's type and value mention (`deps`), the lemmas its proofs call
  included: the closure [trust](https://github.com/chrisflav/trust) draws. -/
  | term
deriving Repr, BEq, Inhabited

/-- A declaration `Context.closure` reached, with its dependencies. -/
structure Reached where
  name : Name
  info : ConstantInfo
  /-- Whether it is a proof: a theorem, or a declaration whose type is a proposition. -/
  isProp : Bool
  deps : DeclDeps
deriving Inhabited

/-- The dependencies `follow` takes out of `r`. -/
def Follow.targets (follow : Follow) (r : Reached) : Array Name :=
  if r.isProp then r.deps.typeDeps
  else match follow with
    | .statement => r.deps.typeDeps
    | .meaning => r.deps.dataDeps
    | .term => r.deps.deps

/-- Whether the declaration `info` is a proof: a theorem, or one whose type is a proposition. -/
def isProofDecl (info : ConstantInfo) : MetaM Bool := do
  if info matches .thmInfo _ then return true
  try Meta.isProp info.type catch _ => return false

/-- Every declaration reachable from `roots` along `follow`, with its dependencies: breadth-first, a
level at a time, each level's dependencies computed in parallel (`depsOf`). The roots come first,
then each level in the order it was reached. Also returns the context, which now holds the data
values the walk computed.

It leaves the project only under `Boundary.none`. Under `Boundary.project` an upstream declaration
the walk reaches is returned with no dependencies, and the walk stops there.

`forProofs` and `forData` name lists to compute besides what `follow` needs, for proofs and for
everything else. By default nothing more: for a proof, `typeDeps` is all that is followed, and
walking its proof term (`deps`) would be most of the cost of the walk. -/
def Context.closure (ctx : Context) (roots : Array Name) (follow : Follow := .meaning)
    (forProofs : DepsRequest := { deps := false, dataDeps := false })
    (forData : DepsRequest := { deps := false, dataDeps := false }) :
    MetaM (Array Reached × Context) := do
  let forData := match follow with
    | .statement => forData
    | .meaning => { forData with dataDeps := true }
    | .term => { forData with deps := true }
  let mut ctx := ctx
  let mut seen : Std.HashSet Name := {}
  let mut frontier : Array Name := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      frontier := frontier.push r
  let mut out : Array Reached := #[]
  while !frontier.isEmpty do
    let infos := frontier.filterMap fun n => (ctx.env.find? n).map (n, ·)
    let props ← infos.mapM fun (_, info) => isProofDecl info
    let analysed (n : Name) := ctx.options.boundary == .none || ctx.declModule.contains n
    let proofs := (infos.zip props).filterMap fun (ni, p) => if p && analysed ni.1 then some ni else none
    let data := (infos.zip props).filterMap fun (ni, p) => if p || !analysed ni.1 then none else some ni
    if forData.dataDeps then
      ctx ← ctx.withDataValuesFor (data.map (·.1))
    let computed := ctx.depsOf proofs forProofs ++ ctx.depsOf data forData
    let byName : Std.HashMap Name DeclDeps := computed.foldl (fun m (n, d) => m.insert n d) {}
    let mut next := #[]
    for ((name, info), isProp) in infos.zip props do
      let r : Reached := { name, info, isProp, deps := byName.getD name ⟨#[], #[], #[]⟩ }
      out := out.push r
      for t in follow.targets r do
        unless seen.contains t do
          seen := seen.insert t
          next := next.push t
    frontier := next
  return (out, ctx)

/-- One-shot entry point: the dependencies of every declaration the project rooted at `rootPrefix`
declares itself. -/
def declDepsOf (env : Environment) (rootPrefix : Name) : Array (Name × DeclDeps) :=
  (Context.of env rootPrefix).allDeclDeps

/-! ## Graph passes

These operate on the dependency graph alone — an `Array (Name × Array Name)` of edges, or the same
data as a `Std.HashMap` — so the caller chooses which edges count. A consumer that treats a
theorem's proof as opaque, for instance, feeds `typeDeps` for theorems and `deps` for everything
else, and every pass then agrees on that choice.
-/

/-- Reverses the edges of `nodes`, keeping only edges whose target is itself one of the `nodes`
(a dependency on something outside the graph — an upstream library constant — has no reverse edge
to record). Each entry lists its users in the order they appear in `nodes`. -/
def reverseDeps (nodes : Array (Name × Array Name)) : Std.HashMap Name (Array Name) :=
  let known : Std.HashSet Name := nodes.foldl (fun s (n, _) => s.insert n) {}
  nodes.foldl
    (fun acc (name, deps) =>
      deps.foldl
        (fun inner dep =>
          if known.contains dep then
            inner.insert dep ((inner.getD dep #[]).push name)
          else
            inner)
        acc)
    {}

/-- The walk state: which nodes have been entered, and the post-order emitted so far. -/
abbrev VisitState := Std.HashSet Name × Array Name

/-- The depth-first walk `topologicalClosure` runs, with an explicit `fuel` bounding the recursion
*depth* so that this is a total definition rather than a `partial` one.

Fuel is what makes the recursion structural. It is not a safety valve: `topologicalClosure` passes
`depsMap.size + 1`, and `Proofs/Deps.lean` proves that is always enough — recursion descends only
from a node that has dependencies, hence is a key of `depsMap`, and never twice from the same key,
so the depth cannot exceed the number of keys. Running out is therefore unreachable, and the
`0` case below is what a proof discharges rather than what a run relies on. -/
def visitFuel (depsMap : Std.HashMap Name (Array Name)) :
    Nat → VisitState → Name → VisitState
  | 0, st, _ => st
  | fuel + 1, (visited, order), n =>
    if visited.contains n then
      (visited, order)
    else
      -- Mark `n` before recursing so a dependency cycle cannot loop forever.
      let visited := visited.insert n
      let (visited, order) :=
        (depsMap.getD n #[]).foldl (fun acc d => visitFuel depsMap fuel acc d) (visited, order)
      -- Emit `n` only after all of its dependencies have been emitted.
      (visited, order.push n)

/-- Computes the declarations reachable from `start` via `depsMap`, in *topological* order: every
declaration appears after all of the declarations it depends on (a depth-first post-order). This is
the order in which the declarations could be emitted into a single self-contained Lean file, with
each definition preceding its first use.

Cycles (e.g. mutual recursion) are tolerated: a node is marked visited on entry, so the walk
terminates, and the members of a cycle come out in some arbitrary but otherwise dependency-respecting
order. -/
def topologicalClosure (depsMap : Std.HashMap Name (Array Name)) (start : Array Name) :
    Array Name :=
  (start.foldl (fun acc n => visitFuel depsMap (depsMap.size + 1) acc n) (({}, #[]) : VisitState)).2

/-- The transitive closure of `name`'s dependencies, topologically ordered (every dependency before
the declarations that use it) and excluding `name` itself, so it is directly usable as the body of
a minimal standalone file for `name`. -/
def transitiveDeps (depsMap : Std.HashMap Name (Array Name)) (name : Name) : Array Name :=
  (topologicalClosure depsMap (depsMap.getD name #[])).filter (· != name)

end MeaningGraph
