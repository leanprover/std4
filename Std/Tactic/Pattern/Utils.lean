/-
Copyright (c) 2023 Anand Rao Tadipatri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao Tadipatri
-/
import Lean.Elab.Term
import Lean.Elab.Tactic
import Lean.SubExpr
import Lean.Meta.ExprLens
import Lean.Meta.KAbstract
import Lean.HeadIndex

open Lean Meta Elab Tactic

/-!

Basic utilities for tactics that target goal locations through patterns and their occurrences.

The code here include:
- Functions for expanding syntax for patterns and occurrences into their corresponding expressions
- Code for generating and finding the occurrences of patterns in expressions

The idea of referring to sub-expressions via patterns and occurrences is due to Yaël Dillies.

-/
open Parser.Tactic Conv

/-- Refer to a set of subexpression by specifying a pattern.

For example, if hypothesis `h` says that `1 + (2 + 3) = 1 + (2 + 3)`, then
`(occs := 2 3) _ + _ at h` refers to the two expression `2 + 3`,
because it first skips `1 + (2 + 3)`, and matches with `2 + 3`,
which instantiates the pattern to be `2 + 3`, so the next match is the
second instance of `2 + 3`. -/
syntax patternLocation := optional(occs) term optional(location)

/--
Elaborate a pattern as an `AbstractMVarsResult`.
This follows code from `Lean/Elab/Tactic/Conv/Pattern.lean`. -/
def expandPattern (p : Syntax) : TermElabM AbstractMVarsResult :=
  withReader (fun ctx => { ctx with ignoreTCFailures := true, errToSorry := false }) <|
    Term.withoutModifyingElabMetaStateWithInfo <| withRef p do
      abstractMVars (← Term.elabTerm p none)

/-- Elaborate `occs` syntax as `Occurrences`. -/
def expandOptOccs (stx : Syntax) : TermElabM Occurrences := do
  if stx.isNone then
    return .all
  match stx[0] with
  | `(occs| (occs := *)) => return .all
  | `(occs| (occs := $ids*)) =>
    return .pos <| Array.toList <| ← ids.mapM fun id =>
      let n := id.toNat
      if n == 0 then
        throwErrorAt id "positive integer expected"
      else return n
  | _ => throwError m! "{stx}"

/-- Elaborate the occurrences, pattern and location in a  `patternLocation`. -/
def expandPatternLocation (stx : Syntax) : TermElabM (Occurrences × AbstractMVarsResult × Location) := do
  let occs ← expandOptOccs stx[0]
  let pattern ← expandPattern stx[1]
  let loc := expandOptLocation stx[2]
  return (occs, pattern, loc)
section Expand



end Expand

section PatternsAndOccurrences

/-- The pattern at a given position in an expression.
    Variables under binders are turned into meta-variables in the pattern. -/
def SubExpr.patternAt (p : SubExpr.Pos) (root : Expr) : MetaM Expr := do
  let e ← Core.viewSubexpr p root
  let binders ← Core.viewBinders p root
  let mvars ← binders.mapM fun (name, type) =>
    mkFreshExprMVar type (userName := name)
  return e.instantiateRev mvars

/-- Finds the occurrence number of the pattern in the expression
    that matches the sub-expression at the specified position.
    This follows the code of `kabstract` from Lean core. -/
def findMatchingOccurrence (position : SubExpr.Pos) (root : Expr) (pattern : Expr) : MetaM Nat := do
  let root ← instantiateMVars root
  unless ← isDefEq pattern (← SubExpr.patternAt position root) do
    throwError s!"The specified pattern does not match the pattern at position {position}."
  let pattern ← instantiateMVars pattern
  let pHeadIdx := pattern.toHeadIndex
  let pNumArgs := pattern.headNumArgs
  let rec
  /-- The recursive step in the expression traversal to search for matching occurrences. -/
  visit (e : Expr) (p : SubExpr.Pos) (offset : Nat) := do
    let visitChildren : Unit → StateRefT Nat (OptionT MetaM) Unit := fun _ => do
      match e with
      | .app f a         => do
        visit f p.pushAppFn offset <|>
        visit a p.pushAppArg offset
      | .mdata _ b       => visit b p offset
      | .proj _ _ b      => visit b p.pushProj offset
      | .letE _ t v b _  => do
        visit t p.pushLetVarType offset <|>
        visit v p.pushLetValue offset <|>
        visit b p.pushLetBody (offset+1)
      | .lam _ d b _     => do
        visit d p.pushBindingDomain offset <|>
        visit b p.pushBindingBody (offset+1)
      | .forallE _ d b _ => do
        visit d p.pushBindingDomain offset <|>
        visit b p.pushBindingBody (offset+1)
      | _                => failure
    if e.hasLooseBVars then
      visitChildren ()
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren ()
    else if (← isDefEq e pattern) then
      let i ← get
      set (i+1)
      if p = position then
        return ()
      else
        visitChildren ()
    else
      visitChildren ()
  let .some (_, occ) ← visit root .root 0 |>.run 0 |
    throwError s!"Could not find pattern at specified position {position}."
  return occ

/-- Finds the occurrence number of the pattern at
    the specified position in the whole expression. -/
def findOccurrence (position : SubExpr.Pos) (root : Expr) : MetaM Nat := do
  let pattern ← SubExpr.patternAt position root
  findMatchingOccurrence position root pattern

end PatternsAndOccurrences

/-- Substitute occurrences of a pattern in an expression with the result of `replacement`. -/
def substitute (e : Expr) (pattern : AbstractMVarsResult) (occs : Occurrences)
    (replacement : Expr → MetaM Expr) (withoutErr : Bool := true) : MetaM Expr := do
  let (_, _, p) ← openAbstractMVarsResult pattern
  let eAbst ← kabstract e p occs
  unless eAbst.hasLooseBVars || withoutErr do
    throwError m!"Failed to find instance of pattern {indentExpr p} in {indentExpr e}."
  instantiateMVars <| Expr.instantiate1 eAbst (← replacement p)

/-- Replace a pattern at the specified locations with the value of `replacement`,
    which is assumed to be definitionally equal to the original pattern. -/
def replaceOccurrencesDefEq (tacticName : Name) (location : Location) (occurrences : Occurrences)
    (pattern : AbstractMVarsResult) (replacement : Expr → MetaM Expr) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    withLocation location
      (atLocal := fun fvarId => do
        let hypType ← fvarId.getType
        let newGoal ← goal.replaceLocalDeclDefEq fvarId <| ←
          substitute hypType pattern occurrences replacement
        replaceMainGoal [newGoal])
      (atTarget := do
        let newGoal ← goal.replaceTargetDefEq <| ←
          substitute (← goal.getType) pattern occurrences replacement
        replaceMainGoal [newGoal])
      (failed := (throwTacticEx tacticName · m!"Failed to run tactic {tacticName}."))
