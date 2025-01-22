import Mrs.Basic
import Mrs.PwlTypes 
import Mrs.PwlTransformShared
import Mrs.PwlTransformLambdaRestructure_Types
import Mrs.Hof
import Util.InsertionSort
import Lean.Data.RBTree

namespace PWL.Transform.LambdaRestructure

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open HOF
open Lean

instance : BEq LambdaConsolidation where
  beq a b := a.targetVar == b.targetVar && 
             a.sources == b.sources &&
             a.scope == b.scope &&
             a.bodyContent == b.bodyContent &&
             a.preservedScopes == b.preservedScopes

/-- Check if one lambda's variables can access another's scope -/
partial def isAccessibleFrom (source : Var) (target : Var) (f : Formula) : Bool :=
  let rec checkAccess (f : Formula) (inScope : Bool) : Bool :=
    match f with
    | Formula.scope vars q inner =>
      if vars.contains source then
        -- Check if target is in accessible scope
        checkAccess inner true
      else if vars.contains target then
        -- Found target scope - only accessible if we're in source scope
        inScope
      else
        checkAccess inner inScope
    | Formula.conj fs =>
      fs.any (fun f => checkAccess f inScope)
    | _ => false

  checkAccess f false

/-- Find variables referenced between consolidations -/
def findSharedVars (a : LambdaConsolidation) (b : LambdaConsolidation) 
    : List Var :=
  let aVars := (a.sources.map (·.2)).join.eraseDups
  let bVars := (b.sources.map (·.2)).join.eraseDups
  aVars.filter (fun v => bVars.contains v)

/-- Determine order dependencies between consolidations -/
partial def findDependencyOrder (consolidations : List LambdaConsolidation) 
    (f : Formula) : List LambdaConsolidation :=
  -- Build dependency graph
  let deps := consolidations.map fun c =>
    let requires := consolidations.filter fun other =>
      c.targetVar != other.targetVar &&
      (findSharedVars c other).any fun v => 
        isAccessibleFrom other.targetVar c.targetVar f
    (c, requires)

  -- Topologically sort based on dependencies
  let rec sortByDeps (remaining : List (LambdaConsolidation × List LambdaConsolidation))
      (done : List LambdaConsolidation) 
      : List LambdaConsolidation :=
    match remaining with
    | [] => done.reverse
    | _ =>
      -- Find node with no remaining dependencies
      match remaining.find? (fun (_, deps) => 
        deps.all (fun d => done.contains d)) with
      | some (next, _) =>
        -- Remove this node from remaining deps
        let newRemaining := remaining.filter (fun (c, _) => 
          c.targetVar != next.targetVar)
        |>.map (fun (c, deps) => 
          (c, deps.filter (·.targetVar != next.targetVar)))
        sortByDeps newRemaining (next :: done)
      | none =>
        -- Cycle detected - pick first remaining
        let (next, _) := remaining.head!
        let newRemaining := remaining.tail!
        |>.map (fun (c, deps) => 
          (c, deps.filter (·.targetVar != next.targetVar)))
        sortByDeps newRemaining (next :: done)

  sortByDeps deps []

/-- Check if consolidations can be merged -/
def canMergeConsolidations (a : LambdaConsolidation) (b : LambdaConsolidation)
    : Bool :=
  -- Consolidations can merge if they share variables and don't conflict
  let shared := findSharedVars a b
  !shared.isEmpty &&  -- Must share variables
  -- Must not have conflicting preserved scopes
  !(a.preservedScopes.any (fun v => b.preservedScopes.contains v)) &&
  -- Must not have conflicting sources
  !(a.sources.any (fun (v,_) => b.sources.any (fun (v2,_) => v == v2)))

/-- Attempt to merge consolidations -/
def mergeConsolidations (a : LambdaConsolidation) (b : LambdaConsolidation)
    : Option LambdaConsolidation :=
  if !canMergeConsolidations a b then none
  else some
    { targetVar := a.targetVar  -- Keep first target
    , sources := a.sources ++ b.sources
    , scope := match (a.scope, b.scope) with
      | (some s1, _) => some s1  -- Keep first scope
      | (none, some s) => some s
      | (none, none) => none
    , bodyContent := match (a.bodyContent, b.bodyContent) with
      | (some c1, some c2) => some (Formula.conj [c1, c2])
      | (some c, none) => some c
      | (none, some c) => some c
      | (none, none) => none
    , preservedScopes := a.preservedScopes ++ b.preservedScopes
    }

/-- Try to combine consolidations where possible -/
partial def combineConsolidations (consolidations : List LambdaConsolidation)
    (f : Formula) : List LambdaConsolidation :=
  -- First order by dependencies
  let ordered := findDependencyOrder consolidations f

  -- Try to merge in order
  let rec combine (remaining : List LambdaConsolidation)
      (done : List LambdaConsolidation) 
      : List LambdaConsolidation :=
    match remaining with
    | [] => done.reverse
    | next :: rest =>
      -- Try to merge with any previous consolidation
      match done.find? (canMergeConsolidations · next) with
      | some prev =>
        match mergeConsolidations prev next with
        | some merged => 
          -- Remove prev and continue with merged
          combine rest (merged :: (done.filter (·.targetVar != prev.targetVar)))
        | none => combine rest (next :: done)
      | none => combine rest (next :: done)

  combine ordered []

end PWL.Transform.LambdaRestructure

export PWL.Transform.LambdaRestructure (
  isAccessibleFrom
  findDependencyOrder 
  combineConsolidations
)
