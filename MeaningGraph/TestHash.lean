import MeaningGraph.Hash

/-!
# The meaning hash, and the graph it is computed with

Checked on declarations of this file. Two versions of a small library are written side by side,
in namespaces `V1` and `V2`: the meaning hash does not depend on names, so what a change does to it
can be read by comparing the two. Not a `module`, like the other tests.

Run with `lake build MeaningGraphTest`.
-/

open Lean Meta MeaningGraph MeaningGraph.Hash

namespace MeaningGraph.TestHash

/-- The walk over `names`, under the suite's rule. -/
def walk (names : Array Name) : MetaM Walk := do
  (Walk.new (← getEnv)).visit names

/-- The meaning hash of each of `names`, from one walk. -/
def meanings (names : Array Name) : MetaM (Array UInt64) := do
  let w ← walk names
  return names.map fun n => (w.meaning? n).getD 0

/-- Whether `a` and `b` have the same meaning hash. -/
def same (a b : Name) : MetaM Bool := do
  let hs ← meanings #[a, b]
  return hs[0]! == hs[1]!

/-- The declarations `n`'s content reaches, looking through helpers. -/
def targets (n : Name) (statement := false) : MetaM (Array Name) := do
  let w ← walk #[n]
  let some b := w.blocks.get? (blockHead w.env n) | return #[]
  return (w.targets (if statement then b.statementMentions else b.mentions)).1

/-! ## What the hash leaves out -/

def PosNat := { n : Nat // 0 < n }
def one₁ : PosNat := ⟨1, Nat.one_pos⟩
def one₂ : PosNat := ⟨1, by decide⟩
def two : PosNat := ⟨2, by decide⟩

theorem addZero₁ {a : Nat} : a + 0 = a := rfl
theorem addZero₂ (b : Nat) : b + 0 = b := by simp

-- Proofs, binder names and binder kinds are not meaning; the value is.
/-- info: (true, false, true) -/
#guard_msgs in
#eval show MetaM _ from do
  return (← same ``one₁ ``one₂, ← same ``one₁ ``two, ← same ``addZero₁ ``addZero₂)

-- A proof inside a statement is erased: what it mentions is not a dependency. (The ascription to
-- `PosNat` is not in the elaborated statement, `Subtype` is.)
theorem valOne : (⟨1, Nat.one_pos⟩ : PosNat).val = 1 := rfl

/-- info: (false, true) -/
#guard_msgs in
#eval show MetaM _ from do
  let ts ← targets ``valOne
  return (ts.contains ``Nat.one_pos, ts.contains ``Subtype)

-- An instance of a `Prop` class is a proof: an argument it fills is erased.
class Good (n : Nat) : Prop where
  pos : 0 < n
instance : Good 1 := ⟨by decide⟩
def needsGood (n : Nat) [Good n] : Nat := n
def usesGood : Nat := needsGood 1

/-- info: (true, false) -/
#guard_msgs in
#eval show MetaM _ from do
  let ts ← targets ``usesGood
  return (ts.contains ``needsGood, ts.contains ``instGoodOfNatNat)

/-! ## Declarations and helpers -/

private def secret : Nat := 3
def revealsSecret : Nat := secret + 1

def byCases : Nat → Nat
  | 0 => 1
  | n + 1 => n

-- A private declaration is a declaration; a matcher is a helper, looked through.
/-- info: (true, true, false, true) -/
#guard_msgs in
#eval show MetaM _ from do
  let env ← getEnv
  let secretName := (env.constants.map₂.toList.find? fun (n, _) =>
    privateToUserName n == `MeaningGraph.TestHash.secret).map (·.1) |>.getD .anonymous
  let ts ← targets ``revealsSecret
  let bs ← targets ``byCases
  return (isDeclaration env secretName (env.find? secretName).get!, ts.contains secretName,
    bs.any (·.toString.endsWith "match_1"), bs.all fun t => (env.find? t).any (isDeclaration env t ·))

-- A constructor is a reference to its inductive type.
def mkPos : PosNat := Subtype.mk 3 (by decide)

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do return (← targets ``mkPos).contains ``Subtype

/-! ## A change changes exactly what rests on it

Version 2 changes `base`. What mentions it, directly or not, changes meaning hash; nothing else
does. Version 3 changes only proofs, and a binder name. -/

namespace V1
def base (n : Nat) : Nat := n + 1
def uses (n : Nat) : Nat := base n * 2
theorem aboutUses : uses 0 = 2 := rfl
def other (n : Nat) : Nat := n * 3
theorem aboutOther : other 1 = 3 := rfl
structure S where
  x : Nat
  h : base x > 0
def mkS : S := ⟨0, by decide⟩
def pair : Nat × Nat := (other 1, 2)
end V1

namespace V2
def base (n : Nat) : Nat := 1 + n
def uses (n : Nat) : Nat := base n * 2
theorem aboutUses : uses 0 = 2 := rfl
def other (n : Nat) : Nat := n * 3
theorem aboutOther : other 1 = 3 := rfl
structure S where
  x : Nat
  h : base x > 0
def mkS : S := ⟨0, by decide⟩
def pair : Nat × Nat := (other 1, 2)
end V2

namespace V3
def base (m : Nat) : Nat := m + 1
def uses (n : Nat) : Nat := base n * 2
theorem aboutUses : uses 0 = 2 := by decide
def other (n : Nat) : Nat := n * 3
theorem aboutOther : other 1 = 3 := by simp [other]
structure S where
  x : Nat
  h : base x > 0
def mkS : S := ⟨0, Nat.succ_pos 0⟩
def pair : Nat × Nat := (other 1, 2)
end V3

def library : List String := ["base", "uses", "aboutUses", "other", "aboutOther", "S", "S.mk", "mkS", "pair"]

/-- The declarations of `library` whose meaning hash differs between versions `a` and `b`. -/
def changed (a b : Name) : MetaM (List String) := do
  let names (v : Name) := library.toArray.map fun s => v ++ s.toName
  let ha ← meanings (names a)
  let hb ← meanings (names b)
  return (library.zip (ha.zip hb).toList).filterMap fun (s, x, y) => if x != y then some s else none

/-- info: ["base", "uses", "aboutUses", "S", "S.mk", "mkS"] -/
#guard_msgs in
#eval changed `MeaningGraph.TestHash.V1 `MeaningGraph.TestHash.V2

/-- info: [] -/
#guard_msgs in
#eval changed `MeaningGraph.TestHash.V1 `MeaningGraph.TestHash.V3

/-- What rests on `base`, by the graph: the declarations of `V1` whose closure reaches it. -/
def restsOnBase : MetaM (List String) := do
  let v := `MeaningGraph.TestHash.V1
  let mut out := []
  for s in library do
    let mut seen : Std.HashSet Name := {}
    let mut todo := #[v ++ s.toName]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      for t in ← targets n do
        if !seen.contains t then
          seen := seen.insert t
          todo := todo.push t
    if s == "base" || seen.contains (v ++ `base) then out := out ++ [s]
  return out

-- The same list: the graph and the hash agree. (`S.mk` is not a declaration; it rests on `base`
-- through `S`.)
/-- info: ["base", "uses", "aboutUses", "S", "S.mk", "mkS"] -/
#guard_msgs in
#eval restsOnBase

/-! ## The local hash -/

/-- The local hash of `n`. -/
def localOf (n : Name) : MetaM UInt64 := do
  let w ← walk #[n]
  return (w.localHash {} n).1

-- References to other declarations are by name: `V1.uses` and `V2.uses` have the same text, but
-- refer to different names, so differ; `V1.other`'s and `V2.other`'s are the same.
/-- info: (false, true) -/
#guard_msgs in
#eval show MetaM _ from do
  return ((← localOf ``V1.uses) == (← localOf ``V2.uses),
    (← localOf ``V1.other) == (← localOf ``V2.other))

-- It changes with the declaration's own content, whatever its dependencies' content.
/-- info: (true, false) -/
#guard_msgs in
#eval show MetaM _ from do
  let w ← walk #[``V1.uses, ``V2.uses]
  -- Pretend `V1.base` had `V2.base`'s content: `V1.uses`' local hash does not move, its meaning
  -- hash would.
  let w' := { w with blocks := w.blocks.insert ``V1.base (w.blocks.get! ``V2.base) }
  return ((w.localHash {} ``V1.uses).1 == (w'.localHash {} ``V1.uses).1,
    (w.meaning? ``V1.uses) == (w.meaning? ``V2.uses))

end MeaningGraph.TestHash
