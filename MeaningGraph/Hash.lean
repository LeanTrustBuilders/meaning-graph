module

public import MeaningGraph.Basic

@[expose] public section

/-!
# One rule for the graph and the hash

What a declaration's meaning depends on, and a hash of that meaning, computed in one walk and from
one rule, so that the two agree by construction (`meaning-hash.md` in LeanTrustBuilders/design).

## The rule (`ltb-meaning/1`)

* **Proofs are erased, everywhere.** In types, in values, in helpers: an argument whose expected
  type is a proposition, and a let-bound value whose type is one, is replaced by a marker. The
  expected type comes from the type of the function applied, so what is left mentions nothing the
  proofs alone mentioned. A declaration whose type is a proposition (a theorem, an instance of a
  `Prop` class, a `Prop`-valued `def`) means its statement.
* **Content.** A definition's content is its type and its (erased) value. A theorem's, an axiom's
  and an opaque constant's is its type. An inductive type is taken with the other types of its
  mutual block and their constructors (a *block*); the recursors follow from them and are not
  hashed. A reference to a constructor or recursor is a reference to its block, and to its position
  in it.
* **Declarations and helpers.** Which constants are declarations — nodes of the graph — is a
  parameter (`Rule.isNode`); by default those a person wrote, private ones included
  (`isDeclaration`). The others are helpers, and are looked through.
* **Edges.** A declaration's edges go to the declarations its content mentions, looking through
  helpers. `statement` edges come from its type alone.
* **The meaning hash** of a constant is a hash of its content in which every reference to another
  constant is replaced by that constant's meaning hash: a Merkle hash. The kernel only lets a
  constant refer to constants before it (or to its own block), so the references form a DAG and
  the hash is well founded. It is deep: it covers everything underneath, upstream included.
  Binder names, binder kinds, metadata and the names of universe parameters are not part of it;
  nor are the names of the constants referred to.
* **The local hash** of a declaration is a hash of the same content with references to other
  declarations, and to the helpers they own, by name. Helpers it owns (named under it:
  `foo.match_1`, `foo._proof_1`, …), and helpers nobody owns, are looked through. It says whether the
  declaration itself was rewritten.

**Consequence.** Whatever `isNode` says, a declaration's meaning hash changes exactly when its own
content (with the helpers it looks through) changes, or the meaning hash of something it refers to
does; and that is exactly when something in its closure along the edges changed (up to 64-bit
collisions). The node rule changes the graph and the local hash, never the meaning hash.

## The content hash (`ltb-content/1`)

The same Merkle hash, from a walk that keeps proofs (`Walk.new env (keepProofs := true)`): nothing
is erased, and a declaration's content is everything the kernel checked of it: a theorem's statement
and proof, a definition's type and value, an opaque constant's type and value, an axiom's type,
inductive blocks as above. Every reference is replaced by the referenced constant's content hash, so
it is deep through proofs: it changes when a proof anywhere underneath changes, which the meaning
hash never does. It leaves out names as the meaning hash does, so it too survives renames.

**Each hash has its graph.** `Walk.edges` gives a declaration's edges from the walk's own blocks:
under the walk that erases proofs, the `statement` and `meaning` edges; under the one that keeps
them, the `term` edges. So the meaning hash follows the `meaning` graph and the content hash the
`term` graph, by construction, whatever the rule's nodes.
-/

open Lean Meta

namespace MeaningGraph.Hash

/-! ## The rule -/

/-- A rule: its name, recorded with the hashes it gave, and which constants are declarations. -/
structure Rule where
  name : String
  isNode : Environment → Name → ConstantInfo → Bool

/-- The suite's rule: declarations are those a person wrote, private ones included. -/
def Rule.meaning : Rule := { name := "ltb-meaning/1", isNode := isDeclaration }

instance : Inhabited Rule := ⟨.meaning⟩

/-- The same, with the declarations completion offers (trust's rule, `isCompletionVisible`). -/
def Rule.completion : Rule :=
  { name := "ltb-meaning/1+completion", isNode := fun env n _ => isCompletionVisible env n }

/-- The name of the content hash, the hash of a walk that keeps proofs, recorded with the hashes it
gave. Bump it whenever what that walk hashes changes. -/
def contentHasherName : String := "ltb-content/1"

/-! ## Erasing proofs -/

/-- The name of the marker an erased proof leaves. No constant has it. -/
def proofMarkerName : Name := .str .anonymous "◾"

/-- What an erased proof leaves. Never type-checked: only hashed. -/
def proofMarker : Expr := .const proofMarkerName []

abbrev EraseM := StateRefT (Std.HashMap ExprStructEq Expr) MetaM

/-- `e`, which is not itself a proof, with its proofs erased: every argument whose expected type is a
proposition, and every let-bound value whose type is one, becomes `proofMarker`. The expected type
of an argument is read off the type of the function applied. -/
partial def erase (e : Expr) : EraseM Expr := do
  match e with
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. | .const .. => return e
  | _ =>
  if let some r := (← get).get? e then return r
  let r ← match e with
    | .app .. => do
      let f := e.getAppFn
      let mut out ← erase f
      let mut ty ← inferType f
      for a in e.getAppArgs do
        unless ty.isForall do ty ← whnf ty
        let .forallE _ d b _ := ty | throwError "erase: expected a function type, got{indentExpr ty}"
        let a' ← if ← isProp d then pure proofMarker else erase a
        out := .app out a'
        ty := b.instantiate1 a
      pure out
    | .lam n t b bi => do
      let t' ← erase t
      withLocalDecl n bi t fun x => do
        return .lam n t' ((← erase (b.instantiate1 x)).abstract #[x]) bi
    | .forallE n t b bi => do
      let t' ← erase t
      withLocalDecl n bi t fun x => do
        return .forallE n t' ((← erase (b.instantiate1 x)).abstract #[x]) bi
    | .letE n t v b nondep => do
      let t' ← erase t
      let v' ← if ← isProp t then pure proofMarker else erase v
      withLetDecl n t v (nondep := nondep) fun x => do
        return .letE n t' v' ((← erase (b.instantiate1 x)).abstract #[x]) nondep
    | .mdata m b => pure (.mdata m (← erase b))
    | .proj s i b => pure (.proj s i (← erase b))
    | _ => pure e
  modify (·.insert e r)
  return r

/-- `e` with its proofs erased, or `e` itself, and whether erasing failed (it should not: `e` is
well typed). -/
def eraseOrKeep (e : Expr) : MetaM (Expr × Bool) := do
  try return ((← (erase e).run' {}), false) catch _ => return (e, true)

/-! ## Blocks -/

/-- What kind of content a block has. -/
inductive Kind where
  /-- Its type is a proposition: it means its statement. -/
  | prop
  /-- A definition: its type and value. -/
  | defn
  /-- An axiom or opaque constant that is not a proof: its type. -/
  | opaque
  /-- Inductive types, their constructors (and recursors, which follow). -/
  | induct
  /-- A quotient primitive. -/
  | quot
deriving BEq, Repr, Inhabited

def Kind.tag : Kind → UInt64
  | .prop => 1 | .defn => 2 | .opaque => 3 | .induct => 4 | .quot => 5

/-- A constant, or an inductive block, with its content erased. -/
structure Block where
  /-- The block's name: the constant, or the first type of an inductive block. -/
  head : Name
  /-- Its constants, in the order a reference records: the types, their constructors, the
  recursors. -/
  members : Array Name
  kind : Kind
  levelParams : List Name
  /-- The erased expressions: the statement's first (`statementSize` of them), then the rest. -/
  exprs : Array Expr
  statementSize : Nat
  /-- Numbers that shape the content and that the expressions do not show: numbers of parameters,
  indices and constructors, the quotient primitive's kind. -/
  shape : Array Nat
  /-- The constants outside the block that its statement mentions. -/
  statementMentions : Array Name
  /-- The constants outside the block that it mentions. -/
  mentions : Array Name
  /-- Whether erasing its proofs failed somewhere (the content is then kept whole). -/
  eraseFailed : Bool := false
deriving Inhabited

/-- The block `n` belongs to, named by its head. -/
def blockHead (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) =>
    match env.find? v.induct with
    | some (.inductInfo iv) => iv.all.headD v.induct
    | _ => v.induct
  | some (.recInfo v) => v.all.headD n
  | some (.inductInfo v) => v.all.headD n
  | _ => n

/-- The constants `es` mention, and the structures their projections name, outside `members`, in
order of first mention. -/
def mentionsOf (es : Array Expr) (members : Array Name) : Array Name := Id.run do
  let own : Std.HashSet Name := members.foldl (·.insert ·) {}
  let mut seen : Std.HashSet Name := {}
  let mut out := #[]
  for e in es do
    for n in exprUsedConstants e do
      if n != proofMarkerName && !own.contains n && !seen.contains n then
        seen := seen.insert n
        out := out.push n
  return out

/-- Builds the block whose head is `head`, erasing its proofs; or, with `keepProofs`, whole: a
theorem's proof and an opaque constant's value are then part of its content. -/
def mkBlock (head : Name) (keepProofs : Bool := false) : MetaM Block := do
  let env ← getEnv
  let info ← getConstInfo head
  let er (e : Expr) : MetaM (Expr × Bool) := if keepProofs then pure (e, false) else eraseOrKeep e
  let mut failed := false
  match info with
  | .inductInfo v =>
    let inds ← v.all.toArray.mapM getConstInfoInduct
    let ctors ← (inds.flatMap (·.ctors.toArray)).mapM getConstInfoCtor
    let recs := (v.all.toArray.map (·.str "rec") ++
      (Array.range v.numNested).map fun i => head.str s!"rec_{i + 1}").filter env.contains
    let members := inds.map (·.name) ++ ctors.map (·.name) ++ recs
    let mut types := #[]
    for i in inds do
      let (t, f) ← er i.type
      types := types.push t
      failed := failed || f
    let mut exprs := types
    for c in ctors do
      let (t, f) ← er c.type
      exprs := exprs.push t
      failed := failed || f
    return { head, members, kind := .induct, levelParams := v.levelParams, exprs
             statementSize := types.size
             shape := #[v.numParams] ++ inds.flatMap (fun i => #[i.numIndices, i.ctors.length])
             statementMentions := mentionsOf types members, mentions := mentionsOf exprs members
             eraseFailed := failed }
  | .quotInfo v =>
    let exprs := #[v.type]
    let k := match v.kind with | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
    return { head, members := #[head], kind := .quot, levelParams := v.levelParams, exprs
             statementSize := 1, shape := #[k], statementMentions := mentionsOf exprs #[head]
             mentions := mentionsOf exprs #[head] }
  | _ =>
    if keepProofs then
      let (kind, exprs) := match info with
        | .thmInfo v => (Kind.prop, #[info.type, v.value])
        | .defnInfo v => (Kind.defn, #[info.type, v.value])
        | .opaqueInfo v => (Kind.opaque, #[info.type, v.value])
        | _ => (Kind.opaque, #[info.type])
      return { head, members := #[head], kind, levelParams := info.levelParams, exprs
               statementSize := 1, shape := #[], statementMentions := mentionsOf #[info.type] #[head]
               mentions := mentionsOf exprs #[head] }
    let isProp ← (do if info matches .thmInfo _ then return true else Meta.isProp info.type) <|>
      pure false
    let (type, f₁) ← eraseOrKeep info.type
    failed := failed || f₁
    let (kind, exprs) ← match info, isProp with
      | _, true => pure (Kind.prop, #[type])
      | .defnInfo v, false =>
        let (value, f₂) ← eraseOrKeep v.value
        failed := failed || f₂
        pure (Kind.defn, #[type, value])
      | _, false => pure (Kind.opaque, #[type])
    return { head, members := #[head], kind, levelParams := info.levelParams, exprs
             statementSize := 1, shape := #[], statementMentions := mentionsOf #[type] #[head]
             mentions := mentionsOf exprs #[head], eraseFailed := failed }

/-! ## Hashing -/

/-- A universe level, with parameters by position. -/
def hashLevel (lps : List Name) : Level → UInt64
  | .zero => 11
  | .succ l => mixHash 12 (hashLevel lps l)
  | .max a b => mixHash 13 (mixHash (hashLevel lps a) (hashLevel lps b))
  | .imax a b => mixHash 14 (mixHash (hashLevel lps a) (hashLevel lps b))
  | .param n => mixHash 15 (lps.idxOf n).toUInt64
  | .mvar _ => 16

abbrev HashM := StateM (Std.HashMap ExprStructEq UInt64)

/-- An expression, with each reference to a constant hashed by `ref`. Binder names and kinds, and
metadata, are left out. Memoised, so linear in the number of distinct subterms: an expression can
share subterms so much that it is a tree of 10⁸ nodes on a few hundred (Tau Ceti's F4 root system).
The match arms must produce their value with `pure`: a `return` would leave the function before the
result is memoised. -/
partial def hashExpr (lps : List Name) (ref : Name → UInt64) (e : Expr) : HashM UInt64 := do
  if let some h := (← get).get? e then return h
  let h ← match e with
    | .bvar i => pure (mixHash 21 i.toUInt64)
    | .sort l => pure (mixHash 22 (hashLevel lps l))
    | .const n ls =>
      if n == proofMarkerName then pure 23
      else pure (mixHash 24 (ls.foldl (fun acc l => mixHash acc (hashLevel lps l)) (ref n)))
    | .app f a => pure <| mixHash 25 (mixHash (← hashExpr lps ref f) (← hashExpr lps ref a))
    | .lam _ t b _ => pure <| mixHash 26 (mixHash (← hashExpr lps ref t) (← hashExpr lps ref b))
    | .forallE _ t b _ => pure <| mixHash 27 (mixHash (← hashExpr lps ref t) (← hashExpr lps ref b))
    | .letE _ t v b _ =>
      pure <| mixHash 28 (mixHash (← hashExpr lps ref t)
        (mixHash (← hashExpr lps ref v) (← hashExpr lps ref b)))
    | .lit (.natVal n) => pure (mixHash 29 (hash n))
    | .lit (.strVal s) => pure (mixHash 30 (hash s))
    | .mdata _ b => hashExpr lps ref b
    | .proj s i b => pure <| mixHash 31 (mixHash (ref s) (mixHash i.toUInt64 (← hashExpr lps ref b)))
    | .fvar _ | .mvar _ => pure 32
  modify (·.insert e h)
  return h

/-- A block's hash, with references outside it hashed by `ref`; a reference to one of its own
constants is by position. -/
def Block.hash (b : Block) (ref : Name → UInt64) : UInt64 :=
  let own : Std.HashMap Name Nat := b.members.foldl (fun m n => m.insert n m.size) {}
  let ref' (n : Name) : UInt64 := match own.get? n with
    | some i => mixHash 41 i.toUInt64
    | none => ref n
  let es := (b.exprs.mapM (hashExpr b.levelParams ref')).run' {}
  let body := es.foldl mixHash (b.shape.foldl (fun acc k => mixHash acc k.toUInt64)
    (mixHash b.kind.tag b.levelParams.length.toUInt64))
  mixHash body b.exprs.size.toUInt64

/-- A name's hash, for references by name. -/
def hashName (n : Name) : UInt64 := mixHash 51 (hash n.toString)

/-! ## The walk -/

/-- Everything the walk computed: blocks and their hashes, for every constant reached. The hashes
are meaning hashes, or content hashes for a walk that keeps proofs. -/
structure Walk where
  rule : Rule
  env : Environment
  /-- Whether proofs are kept: the walk then reaches everything proofs mention, and its hash is the
  content hash (`ltb-content/1`) instead of the meaning hash. -/
  keepProofs : Bool := false
  blocks : Std.HashMap Name Block := {}
  /-- Each constant reached ↦ its block's head and its position in the block. -/
  position : Std.HashMap Name (Name × Nat) := {}
  /-- Each block ↦ its hash. -/
  blockHash : Std.HashMap Name UInt64 := {}
  /-- References that were not hashed before the block referring to them (a cycle, which the
  kernel does not allow), hashed by name instead. Should be 0. -/
  unresolved : Nat := 0

/-- The hash of a constant the walk reached: its block's, and its position in it. The meaning hash,
or the content hash if the walk keeps proofs. -/
def Walk.hash? (w : Walk) (n : Name) : Option UInt64 := do
  let (h, i) ← w.position.get? n
  let bh ← w.blockHash.get? h
  return if i == 0 then bh else mixHash bh i.toUInt64

/-- The meaning hash of a constant a walk that erases proofs reached. -/
def Walk.meaning? (w : Walk) (n : Name) : Option UInt64 := w.hash? n

/-- The content hash of a constant a walk that keeps proofs reached. -/
def Walk.content? (w : Walk) (n : Name) : Option UInt64 := w.hash? n

/-- Walks everything `roots` rest on and hashes it, reusing what `w` already has: blocks are built
(proofs erased) the first time they are reached, and hashed once everything they mention is. -/
def Walk.visit (w : Walk) (roots : Array Name) : MetaM Walk := do
  let env := w.env
  let mut w := w
  let mut started : Std.HashSet Name := {}
  let mut stack : Array (Name × Bool) := roots.reverse.map fun r => (blockHead env r, false)
  while !stack.isEmpty do
    let (h, done) := stack.back!
    stack := stack.pop
    if done then
      let some b := w.blocks.get? h | continue
      let mut unresolved := 0
      for m in b.mentions do
        if (w.hash? m).isNone then unresolved := unresolved + 1
      let ref (n : Name) : UInt64 := (w.hash? n).getD (hashName n)
      w := { w with blockHash := w.blockHash.insert h (b.hash ref), unresolved := w.unresolved + unresolved }
      continue
    if w.blockHash.contains h || started.contains h || !env.contains h then continue
    started := started.insert h
    let b ← mkBlock h w.keepProofs
    w := { w with blocks := w.blocks.insert h b
                  position := (b.members.zipIdx).foldl (fun m (n, i) => m.insert n (h, i)) w.position }
    stack := stack.push (h, true)
    for m in b.mentions.reverse do
      let mh := blockHead env m
      if !w.blockHash.contains mh && !started.contains mh then stack := stack.push (mh, false)
  return w

/-- A new walk under `rule`, which erases proofs unless `keepProofs`. -/
def Walk.new (env : Environment) (rule : Rule := .meaning) (keepProofs := false) : Walk :=
  { rule, env, keepProofs }

/-- Whether a constant the walk reached is a declaration under its rule. -/
def Walk.isNode (w : Walk) (n : Name) : Bool :=
  match w.env.find? n with
  | some info => w.rule.isNode w.env n info
  | none => false

/-- The declaration a reference to `n` points to, if `n` is one or belongs to one: a constructor or
recursor points to its inductive type, if that is a declaration. -/
def Walk.nodeFor? (w : Walk) (n : Name) : Option Name :=
  if w.isNode n then some n
  else match w.env.find? n with
    | some (.ctorInfo v) => if w.isNode v.induct then some v.induct else none
    | some (.recInfo v) =>
      -- `T.rec`, `T.rec_1`: the type it is named under, else the block's first
      let t := n.getPrefix
      if v.all.contains t && w.isNode t then some t
      else v.all.find? w.isNode
    | _ => none

/-- The declarations `names` point to, looking through helpers: what the walk's edges are. The memo
maps each helper block to the declarations it reaches. -/
partial def Walk.targets (w : Walk) (names : Array Name)
    (memo : Std.HashMap Name (Array Name) := {}) : Array Name × Std.HashMap Name (Array Name) :=
  Id.run do
    let mut memo := memo
    let mut seen : Std.HashSet Name := {}
    let mut out := #[]
    for n in names do
      if let some t := w.nodeFor? n then
        if !seen.contains t then
          seen := seen.insert t
          out := out.push t
      else
        let h := blockHead w.env n
        let ts ← match memo.get? h with
          | some ts => pure ts
          | none =>
            -- Mark the helper first: helpers do not refer to each other in cycles, but a block
            -- of mutual helpers would otherwise loop.
            memo := memo.insert h #[]
            let (ts, memo') := w.targets ((w.blocks.get? h).map (·.mentions) |>.getD #[]) memo
            memo := memo'.insert h ts
            pure ts
        for t in ts do
          if !seen.contains t then
            seen := seen.insert t
            out := out.push t
    return (out, memo)

/-- The edges of `n`, which the walk has visited: the declarations its statement mentions, and those
its whole content mentions, looking through helpers (`targets`); an inductive type also rests on the
other types of its mutual block that are declarations. Under a walk that erases proofs these are the
`statement` and `meaning` edges, which the meaning hash follows; under one that keeps proofs, the
content ones are the `term` edges, which the content hash follows. The memo is `targets`'. -/
def Walk.edges (w : Walk) (n : Name) (memo : Std.HashMap Name (Array Name) := {}) :
    (Array Name × Array Name) × Std.HashMap Name (Array Name) :=
  match w.blocks.get? (blockHead w.env n) with
  | none => ((#[], #[]), memo)
  | some b =>
    let (statement, memo) := w.targets b.statementMentions memo
    let (content, memo) := w.targets b.mentions memo
    let siblings := if b.kind == .induct then b.members.filter fun m => m != n && w.isNode m &&
        (w.env.find? m matches some (.inductInfo _)) else #[]
    ((statement.filter (· != n), (content ++ siblings).filter (· != n)), memo)

/-- The private declaration named `p` in the module of `n`, when `n` is private: the owner
`Walk.ownerOf?` tries before the public `p`. A private name with macro scopes has none:
`privatePrefix?` of such a name is the whole name, and `++` panics on two names with macro scopes. -/
def privateCandidate? (n p : Name) : Option Name :=
  ((privatePrefix? n).filter (!·.hasMacroScopes)).map (· ++ p)

/-- The declaration that owns the helper `n`: the longest proper prefix of its name that names a
declaration under the walk's rule; for a private helper, the private declaration of the same module
of that name, or else the public one. It depends on the environment only, not on which declarations
a dataset has as nodes. -/
def Walk.ownerOf? (w : Walk) (n : Name) : Option Name :=
  go (privateToUserName n).getPrefix
where
  found (p : Name) : Option Name :=
    match privateCandidate? n p with
    | some q => if w.isNode q then some q else if w.isNode p then some p else none
    | none => if w.isNode p then some p else none
  go : Name → Option Name
    | .anonymous => none
    | p@(.str q _) => (found p).orElse fun _ => go q
    | p@(.num q _) => (found p).orElse fun _ => go q

/-- The local hash of declaration `d`: its content, with references to other declarations, to
constants outside the walk and to the helpers other declarations own, by name; the helpers it owns
and the helpers nobody owns are looked through, by their own local content. -/
partial def Walk.localHash (w : Walk) (d : Name)
    (memo : Std.HashMap (Name × Name) UInt64 := {}) : UInt64 × Std.HashMap (Name × Name) UInt64 :=
  Id.run do
    let some b := w.blocks.get? (blockHead w.env d) | return (hashName d, memo)
    let mut memo := memo
    let mut refs : Std.HashMap Name UInt64 := {}
    for m in b.mentions do
      let h := blockHead w.env m
      let byName := (w.nodeFor? m).isSome || !w.blocks.contains h ||
        match w.ownerOf? m with
        | some o => o != d
        | none => false
      if byName then
        refs := refs.insert m (hashName m)
      else
        let key := (d, h)
        let hh ← match memo.get? key with
          | some hh => pure hh
          | none =>
            memo := memo.insert key (hashName m)
            let (hh, memo') := w.localHash h memo
            memo := memo'.insert key hh
            pure hh
        let i := ((w.position.get? m).map (·.2)).getD 0
        refs := refs.insert m (if i == 0 then hh else mixHash hh i.toUInt64)
    return (b.hash fun n => refs.getD n (hashName n), memo)

end MeaningGraph.Hash
