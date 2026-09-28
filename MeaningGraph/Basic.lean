module

public import Lean
public import Lean.Meta.Instances

@[expose] public section

/-!
# The basics of the dependency analysis

What the walks of `MeaningGraph.Hash` and the dependency lists of `MeaningGraph.Deps` are built on:

* **which constants are declarations**: `isDeclaration` (a person wrote it, private or not), and
  `isCompletionVisible` (what Lean offers for completion); the others are helpers, looked through;
* **the constants an expression uses** (`exprUsedConstants`), including the structure name of every
  `Expr.proj` node (`projStructureNames`);
* **what a declaration's source needs that its elaborated term does not mention**: the constants a
  notation expands to (`notationExpansionDeps`, stored as `Name` data inside embedded `Syntax`), and
  the coercion instances an elaborated term drops (`coercionInstancesByType`);
* **graph passes** over plain `Name`-keyed maps: reverse edges, and transitive closure in
  topological order.

Lean core only: no Lake, no document format, no notion of a project directory or of output.
-/
open Lean
open Lean.Meta

namespace MeaningGraph

/-! ## Name classification

Which constants are the project's own user-written declarations, and which are compiler output.
This is what bounds the analysis: helper constants are expanded *through* (their dependencies are
pulled in instead of the helper), and everything outside the project is left alone.
-/

/-- True if `s` is `pfx` followed by a digit and then digits and underscores, the naming
convention used by the compiler for auto-generated declarations like `match_1`, `eq_2`,
`hcongr_11`, and `match_1_1` (a second matcher of that name, inside a private declaration). -/
def isPrefixWithDigitSuffix (pfx s : String) : Bool :=
  s.startsWith pfx &&
    let rest := (s.drop pfx.length).toString.toList
    rest.head?.any Char.isDigit && rest.all fun c => c.isDigit || c == '_'

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
constant. -/
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
  else if isAuxRecursor env name || isNoConfusion env name || Meta.isMatcherCore env name then
    false
  else if hasConstructorPrefix env name then
    false
  else match info with
    | .ctorInfo _ | .recInfo _ | .quotInfo _ => false
    | _ => true

/-- Whether a declaration is one a person wrote, private or not: `isAuthored`, except that a private
declaration counts. `isAuthored` reads the `_private` prefix of a private name as the mark of a
helper; here the name is read without it. The suite's rule for which constants are declarations
(`MeaningGraph.Hash.Rule.meaning`). -/
def isDeclaration (env : Environment) (n : Name) (info : ConstantInfo) : Bool :=
  if isPrivateName n then
    let u := privateToUserName n
    !env.isProjectionFn n && !(isInternalName u || u.isInternal || u.isImplementationDetail)
      && !isAuxRecursor env n && !isNoConfusion env n && !Meta.isMatcherCore env n
      && !hasConstructorPrefix env n
      && !(info matches .ctorInfo _ | .recInfo _ | .quotInfo _)
  else isAuthored env n info

/-- Whether a declaration is one the project's author wrote (`isAuthored`) in a module of the project
(`isProjectLocalConst`). -/
def shouldExpose (env : Environment) (rootPrefix : Name) (name : Name) (info : ConstantInfo) : Bool :=
  isProjectLocalConst env rootPrefix name && isAuthored env name info

/-- Whether Lean offers `name` for completion, and it is not an internal detail: the rule
[aftk](https://github.com/mathlib-initiative/aftk)'s `shouldDisplay` states, which
[trust](https://github.com/chrisflav/trust) draws its graphs with. Unlike `isAuthored`, it keeps
constructors, projections, `Quot` primitives and the lemmas Lean generates under ordinary names
(`eq_1`, `eq_def`, `injEq`, `ext_iff`, …). -/
def isCompletionVisible (env : Environment) (name : Name) : Bool :=
  Lean.Meta.allowCompletion env name && !(privateToUserName name).isInternalDetail

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
and `Context.sourceDeps` only replays the instance for declarations that mention all of them. -/
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

/-- Memo table for the one-level expansion of helpers, shared across the declarations of one run
(see `expandThrough`). -/
abbrev Cache := Std.HashMap Name (Array Name)

/-- Expands `start` by looking through every constant `isHelper` accepts: such a constant is
replaced by what it uses (`usedConstantsOf`, value included), recursively, and every other constant
is kept as it is. `cache` memoizes the one-level expansion of helpers across calls. What
`Context.sourceDeps` expands coercion instances and notation through. -/
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

/-! ## Which project modules a module can see -/

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

/-! ## Graph passes

These operate on the dependency graph alone — an `Array (Name × Array Name)` of edges, or the same
data as a `Std.HashMap` — so the caller chooses which edges count. A consumer that treats a
theorem's proof as opaque, for instance, feeds `statement` for theorems and `term` for everything
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
