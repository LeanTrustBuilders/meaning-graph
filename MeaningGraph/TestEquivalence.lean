import MeaningGraph

/-!
# Speed without a change of result

The notation walk was rewritten for speed: it visits each shared subterm once. The original
implementation is kept here as the reference, and the checks below compare the two, on a term with
2⁶⁴ paths and on `Init.Notation`, where `Context.of` works as on any project (124 notations).

Unlike `MeaningGraph.Test`, this file is not a `module`. A module imports others at their exported
level, where definitions come without their values, and the notation table and the value walks
would see nothing. A tool analysing a project imports it in full, and so does this file.

Run with `lake build MeaningGraphTest`.
-/

open Lean MeaningGraph

namespace MeaningGraph.TestEquivalence


/-- `collectEmbeddedNames` as first written: a tree walk, visiting a shared subterm once per path. -/
def treeEmbeddedNames (e : Expr) : Array Name := Id.run do
  let mut acc : Array Name := #[]
  if let some n := evalNameExpr? e then acc := acc.push n
  match e with
  | .app f a => return acc ++ treeEmbeddedNames f ++ treeEmbeddedNames a
  | .lam _ t b _ => return acc ++ treeEmbeddedNames t ++ treeEmbeddedNames b
  | .forallE _ t b _ => return acc ++ treeEmbeddedNames t ++ treeEmbeddedNames b
  | .letE _ t v b _ =>
    return acc ++ treeEmbeddedNames t ++ treeEmbeddedNames v ++ treeEmbeddedNames b
  | .mdata _ b => return acc ++ treeEmbeddedNames b
  | .proj _ _ b => return acc ++ treeEmbeddedNames b
  | _ => return acc

/-- `notationExpansionDeps` as first written, on top of the tree walk. -/
def treeNotationDeps (env : Environment) (projectConsts : Array (Name × Name × ConstantInfo)) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for (_, _, cinfo) in projectConsts do
    if let .defnInfo v := cinfo then
      let names := (treeEmbeddedNames v.value).filter (env.contains ·)
      let kinds := names.filter (isNotationKind env ·)
      unless kinds.isEmpty do
        let realDeps := names.filter (!isNotationKind env ·)
        for k in kinds do
          m := m.insert k ((m.getD k #[]) ++ realDeps)
  return m

/-- First occurrences, in order: what every consumer of these lists keeps. -/
def firstOccurrences (a : Array Name) : Array Name :=
  (a.foldl (fun (seen, out) n => if seen.contains n then (seen, out) else (seen.insert n, out.push n))
    ((({} : Std.HashSet Name)), (#[] : Array Name))).2

/-- A name-building term shared by both sides of every application, `depth` levels deep: `2 ^ depth`
paths to its leaf, but `depth + 1` distinct subterms. -/
def sharedTerm : Nat → Expr
  | 0 => mkApp2 (mkConst ``Lean.Name.mkStr2) (mkStrLit "A") (mkStrLit "b")
  | n + 1 => let e := sharedTerm n; mkApp2 (mkConst ``Prod.mk) e e

-- The memoized walk finds the same names as the tree walk, in the same order of first occurrence.
#guard collectEmbeddedNames (sharedTerm 3) == firstOccurrences (treeEmbeddedNames (sharedTerm 3))
#guard (treeEmbeddedNames (sharedTerm 3)).size == 8   -- `A.b`, once per path
-- 2 ^ 64 paths: only a walk that visits each subterm once finishes.
#guard collectEmbeddedNames (sharedTerm 64) == #[`A.b]
#guard buildsName (sharedTerm 1) && !buildsName (mkConst ``Nat)

-- `moduleNameOf` answers for an imported constant, and not for one of this module.
/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  let env ← getEnv
  return moduleNameOf env ``Nat.add == some `Init.Prelude && moduleNameOf env ``sharedTerm == none

/-- Whether the notation table of the project `root` is the tree walk's, up to repetitions. -/
def sameNotationTable (root : Name) : MetaM Bool := do
  let env ← getEnv
  let ctx := Context.of env root
  let reference := treeNotationDeps env ctx.constants
  return !reference.isEmpty && reference.size == ctx.notationDeps.size &&
    reference.toList.all fun (k, v) =>
      firstOccurrences v == firstOccurrences (ctx.notationDeps.getD k #[])

/-- info: true -/
#guard_msgs in
#eval sameNotationTable `Init.Notation

end MeaningGraph.TestEquivalence
