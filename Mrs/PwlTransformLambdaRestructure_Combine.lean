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

/-- Find scopes that need to be preserved during consolidation -/
partial def findScopesToPreserve (target : Var) (f : Formula) : List Var := 
  let rec findRefs (f : Formula) (inLambda : Bool) : List Var :=
    match f with
    | Formula.atom ep =>
      if isLambdaPredicate ep.predicate then
        match ep.rargs.find? (fun arg => arg.1 == "ARG0") with
        | some (_, outVar) => 
          if outVar == target then
            -- Inside target lambda, collect non-lambda references
            ep.rargs.filter (fun arg => 
              arg.1 != "ARG0" && arg.2.sort == 'x'
            ) |>.map (·.2)
          else []
        | none => []
      else
        -- Only count references outside lambdas
        if !inLambda then
          ep.rargs.filter (fun arg => arg.2 == target) |>.map (·.2)
        else []
    | Formula.scope vars q inner =>
      if vars.contains target then []
      else findRefs inner (inLambda || q == some "lambda")
    | Formula.conj fs =>
      fs.foldl (fun acc f => acc ++ findRefs f inLambda) []

  (findRefs f false).eraseDups

/-- Build consolidated lambda expression -/
def buildConsolidatedLambda (target : LambdaInfo) 
    (sources : List LambdaInfo) : Formula :=
  -- Collect all variables from target and sources
  let allVars := (target.targetVars ++ 
    (sources.map (·.targetVars)).join).eraseDups

  Formula.atom {
    predicate := "implicit_conj",
    label := target.sourceVar,
    rargs := ("ARG0", target.sourceVar) :: 
      (allVars.enum.map fun (i, v) => (s!"ARG{i+1}", v)),
    carg := some "/* consolidated */",
    link := none
  }

def combineBodyContent (target : LambdaInfo) (sources : List LambdaInfo) 
    : Option Formula :=
  dbg_trace s!"COMBINE: Combining body content for target {target.sourceVar}"
  dbg_trace s!"COMBINE: Source bodies: {sources.map fun s => s.bodyContent}"
  
  let contents := sources.filterMap (·.bodyContent)
  let result := match target.bodyContent with
  | none => 
    match contents with
    | [] => none
    | [single] => some single
    | multiple => some (Formula.conj multiple)
  | some targetContent =>
    match contents with
    | [] => some targetContent  
    | cs => some (Formula.conj (targetContent :: cs))

  dbg_trace s!"COMBINE: Combined result: {result}"
  result

/-- Find deepest common scope for a set of variables -/
partial def findCommonScope (f : Formula) (vars : List Var) : Option Var :=
  let rec findScopes (f : Formula) (currentScope : Option Var) 
      : List (Var × List Var) :=
    match f with
    | Formula.scope boundVars q inner =>
      let boundInScope := vars.filter (boundVars.contains ·)
      let innerScopes := findScopes inner (boundVars.head?)
      match boundVars.head? with
      | some v => (v, boundInScope) :: innerScopes
      | none => innerScopes
    | Formula.conj fs =>
      fs.foldl (fun acc f => acc ++ findScopes f currentScope) []
    | _ => []

  -- Find scope that contains most target variables
  let scopes := findScopes f none
  let withCounts := scopes.map (fun (v, bound) => 
    (v, bound.length))
  
  let maxCount := withCounts.foldl (fun max (_, count) =>
    if count > max then count else max) 0

  withCounts.find? (fun (_, count) => count == maxCount)
  |>.map (·.1)

def consolidateLambdas (f : Formula) (target : LambdaInfo) (sources : List LambdaInfo) (lambdas : List LambdaInfo) : LambdaConsolidation :=
  dbg_trace s!"CONSOLIDATE_LAMBDA: Starting consolidation with target={target.sourceVar}"
  dbg_trace s!"CONSOLIDATE_LAMBDA: Sources={sources.map fun s => (s.sourceVar, s.targetVars)}"
  
  -- Expand target vars recursively
  let expandedTargets := target.targetVars.foldl (fun acc v =>
    acc ++ expandLambdaTargets lambdas v) []
  
  -- Expand source targets recursively
  let sourceTargets := sources.foldl (fun acc source =>
    acc ++ (source.targetVars.foldl (fun innerAcc v =>
      innerAcc ++ expandLambdaTargets lambdas v) [])) []
  
  -- Combine and deduplicate all targets
  let consolidatedTargets := (expandedTargets ++ sourceTargets).eraseDups
  
  dbg_trace s!"CONSOLIDATE_LAMBDA: Consolidated targets for {target.sourceVar}: {consolidatedTargets}"

  let preserved := findScopesToPreserve target.sourceVar f
  dbg_trace s!"CONSOLIDATE_LAMBDA: Preserved scopes: {preserved}"

  { targetVar := target.sourceVar
  , sources := sources.map (fun s => (s.sourceVar, consolidatedTargets))
  , scope := some target.sourceVar
  , bodyContent := target.bodyContent
  , preservedScopes := preserved
  , quantifier := some target.predicate }

end PWL.Transform.LambdaRestructure

export PWL.Transform.LambdaRestructure (
  findScopesToPreserve
  consolidateLambdas
)
