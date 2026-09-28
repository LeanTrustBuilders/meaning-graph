module

public import MeaningGraph.Basic
public import MeaningGraph.Hash
public import MeaningGraph.Deps

/-!
# MeaningGraph

What every declaration of a Lean project rests on, and a hash of what it means, from one walk under
one rule, so that each hash follows its graph by construction.

* `MeaningGraph.Basic`: which constants are declarations, the constants an expression uses, what a
  declaration's source needs besides its elaborated term (notation, coercions), and graph passes;
* `MeaningGraph.Hash`: the rule `ltb-meaning/1`, its walks, the meaning, local and content hashes,
  and each walk's edges;
* `MeaningGraph.Deps`: a project's `statement`, `meaning` and `term` dependencies, taken from the
  walks, and closures along them.
-/
