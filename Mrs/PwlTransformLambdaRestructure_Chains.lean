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

/-- Find direct references between two lambdas -/
def findDirectReferences (a : LambdaInfo) (b : LambdaInfo) : Bool :=
  a.targetVars.any (fun v => b.targetVars.contains v)

partial def collectNestedLambdas (f : Formula) (acc : List LambdaInfo) : List LambdaInfo :=
  match f with
  | Formula.atom ep => 
    if isLambdaPredicate ep.predicate then
      match getOutArg ep with
      | some outVar =>
        let targetVars := getTargetVars ep
        let newLambda := { sourceVar := outVar
                         , targetVars := targetVars
                         , predicate := ep.predicate
                         , bodyContent := none
                         , status := LambdaStatus.KeepScope }
        
        dbg_trace s!"LAMBDA_STRUCT: Found lambda definition:"
        dbg_trace s!"  Source: {outVar}"
        dbg_trace s!"  Predicate: {ep.predicate}"
        dbg_trace s!"  Raw args: {ep.rargs}"
        dbg_trace s!"  Direct targets: {targetVars}"
        dbg_trace "  ==="
        
        if acc.any (fun l => l.sourceVar == outVar) then acc
        else newLambda :: acc
      | none => acc
    else acc
        
  | Formula.scope _ _ inner => 
    collectNestedLambdas inner acc
      
  | Formula.conj fs => 
    fs.foldl (fun acc f => collectNestedLambdas f acc) acc

def findLambdaGroups (lambdas : List LambdaInfo) : List (List LambdaInfo) :=
  dbg_trace s!"GROUPS: Starting with lambdas: {lambdas.map fun l => (l.sourceVar, l.targetVars)}"
  
  let rec findGroups (remaining : List LambdaInfo) (acc : List (List LambdaInfo)) : List (List LambdaInfo) :=
    match remaining with
    | [] => acc
    | l :: rest =>
      -- Skip if lambda is already in a group
      if acc.any (fun group => group.any (fun g => g.sourceVar == l.sourceVar)) then
        dbg_trace s!"GROUPS: {l.sourceVar} already grouped, skipping"
        findGroups rest acc
      else
        -- First expand any lambda references in current lambda's targets
        let expandedCurrent := l.targetVars.foldl (fun acc v =>
          match lambdas.find? (fun other => other.sourceVar == v) with
          | some other => 
            dbg_trace s!"GROUPS: Expanding {v} from {l.sourceVar} using {other.sourceVar}'s targets {other.targetVars}"
            acc ++ other.targetVars 
          | none => acc ++ [v]
        ) []
        dbg_trace s!"GROUPS: Expanded current {l.sourceVar} targets: {l.targetVars} -> {expandedCurrent}"
        
        -- Find lambdas that share any variables with this one
        let related := remaining.filter fun r =>
          r.sourceVar == l.sourceVar ||  -- Self reference
          -- Expand other lambda's targets
          let expandedOther := r.targetVars.foldl (fun acc v =>
            match lambdas.find? (fun other => other.sourceVar == v) with
            | some other => 
              dbg_trace s!"GROUPS: Expanding {v} from {r.sourceVar} using {other.sourceVar}'s targets {other.targetVars}"
              acc ++ other.targetVars 
            | none => acc ++ [v]
          ) []
          dbg_trace s!"GROUPS: Expanded other {r.sourceVar} targets: {r.targetVars} -> {expandedOther}"
          
          -- Check overlap using expanded targets
          let hasOverlap := expandedOther.any (fun v => expandedCurrent.contains v) ||
                           expandedCurrent.any (fun v => expandedOther.contains v)
          dbg_trace s!"GROUPS: Checking overlap between {l.sourceVar}({expandedCurrent}) and {r.sourceVar}({expandedOther}): {hasOverlap}"
          hasOverlap
        
        let expandVars (vars : List Var) : List Var :=
          vars.foldl (fun acc v =>
            match lambdas.find? (fun other => other.sourceVar == v) with
            | some other => acc ++ other.targetVars 
            | none => acc ++ [v]
          ) []
        
        let expandTargetVars (r : LambdaInfo) : LambdaInfo :=
          { r with targetVars := expandVars r.targetVars }
        
        let expandedRelated := related.map expandTargetVars
        
        dbg_trace s!"GROUPS: Found final group for {l.sourceVar}: {expandedRelated.map fun r => (r.sourceVar, r.targetVars)}"
        findGroups rest (expandedRelated :: acc)

  findGroups lambdas []

/-- Collect expanded targets for a set of source variables -/
partial def expandAllTargets (lambdas : List LambdaInfo) (sources : List LambdaInfo) : List Var :=
  let sourceVars := sources.map (·.targetVars) |>.join
  dbg_trace s!"EXPAND_ALL: Starting with source vars {sourceVars}"

  let rec expandVar (seen : List Var) (v : Var) : List Var :=
    if seen.contains v then []
    else match lambdas.find? (fun l => l.sourceVar == v) with
      | none => [v]
      | some info => 
        let expanded := info.targetVars.foldl (fun acc targetVar =>
          if seen.contains targetVar then acc 
          else acc ++ expandVar (v :: seen) targetVar
        ) []
        dbg_trace s!"EXPAND_ALL: {v} expands to {expanded}"
        expanded

  let allExpanded := sourceVars.foldl (fun acc v => 
    acc ++ expandVar [] v) []
  
  dbg_trace s!"EXPAND_ALL: Final expanded targets: {allExpanded.eraseDups}"
  allExpanded.eraseDups

def markObsoleteLambdas (groups : List (List LambdaInfo)) : List LambdaInfo :=
  groups.foldl (fun acc group =>
    -- Process each group of related lambdas
    let withStatus := group.map fun l =>
      dbg_trace s!"MARK_GROUP: Processing lambda {l.sourceVar} with targets {l.targetVars}"
      
      -- For a group of lambdas that can be consolidated:
      -- 1. Find the lambda that has the most complete set of targets
      -- 2. Mark others as obsolete if their targets are fully contained
      let hasAllTargets := group.any fun other =>
        if other.sourceVar == l.sourceVar then
          dbg_trace s!"MARK_CHECK: Skipping self-comparison for {l.sourceVar}"
          false
        else
          dbg_trace s!"MARK_CHECK: Checking if {other.sourceVar} contains all targets of {l.sourceVar}"
          -- Check if other lambda contains all this one's variables
          let allContained := l.targetVars.all fun targetVar =>
            other.targetVars.contains targetVar
          dbg_trace s!"MARK_CHECK: All targets contained? {allContained}"
          allContained

      -- Also check if this lambda contains all targets of any other
      let containsAllOthers := group.any fun other =>
        if other.sourceVar == l.sourceVar then false
        else 
          other.targetVars.all fun targetVar =>
            l.targetVars.contains targetVar
            
      if hasAllTargets then
        dbg_trace s!"MARK: {l.sourceVar} subsumed by other lambda, marking Obsolete"
        { l with status := LambdaStatus.Obsolete }
      else if containsAllOthers then 
        dbg_trace s!"MARK: {l.sourceVar} contains all targets, marking KeepScope"
        { l with status := LambdaStatus.KeepScope }
      else
        dbg_trace s!"MARK: {l.sourceVar} independent, marking KeepScope" 
        { l with status := LambdaStatus.KeepScope }

    acc ++ withStatus) []

/-- Create consolidation with all expanded variables -/
def createConsolidation (lambdas : List LambdaInfo) (kept : LambdaInfo) (obsolete : List LambdaInfo) : LambdaConsolidation :=
  -- Get original variables and all expanded variables
  let expandedTargets := expandAllTargets lambdas (kept :: obsolete)
  dbg_trace s!"CREATE_CONS: For {kept.sourceVar} with targets {kept.targetVars}"
  dbg_trace s!"CREATE_CONS: Obsolete: {obsolete.map (·.sourceVar)}"
  dbg_trace s!"CREATE_CONS: All expanded targets: {expandedTargets}"

  { targetVar := kept.sourceVar
  , sources := [(kept.sourceVar, expandedTargets)] ++ 
               (obsolete.map fun o => (o.sourceVar, o.targetVars))
  , scope := some kept.sourceVar  
  , bodyContent := kept.bodyContent
  , preservedScopes := []
  , quantifier := some kept.predicate }

/-- Build consolidation chains for a formula -/
partial def buildConsolidationChains (f : Formula) : List LambdaInfo :=  
  dbg_trace "CHAIN: Building consolidation chains"
  
  -- First collect all lambdas with their direct targets
  let lambdas := collectNestedLambdas f []
  dbg_trace s!"CHAIN: Found initial lambdas: {lambdas}"
  
  -- Group related lambdas  
  let groups := findLambdaGroups lambdas
  dbg_trace s!"CHAIN: Found {groups.length} consolidation groups"
  
  -- Mark obsolete using expanded targets for comparison
  let markedLambdas := markObsoleteLambdas groups
  dbg_trace s!"CHAIN: Final groups marked: {markedLambdas}"

  let (obsolete, kept) := markedLambdas.partition (·.status == LambdaStatus.Obsolete)
  dbg_trace s!"CHAIN: Obsolete lambdas: {obsolete.map (·.sourceVar)}"
  dbg_trace s!"CHAIN: Kept lambdas: {kept.map (·.sourceVar)}"

  -- For each kept lambda, create consolidation with any obsolete lambdas it contains
  let consolidations := kept.map fun k =>
    let obsoleteGroup := obsolete.filter (fun o => containsAllTargets k o lambdas)
    createConsolidation lambdas k obsoleteGroup
  
  markedLambdas.map fun info =>
    match consolidations.find? (fun cons => cons.targetVar == info.sourceVar) with
    | some cons => { info with 
                    targetVars := cons.sources.head!.2,  -- Get expanded targets from consolidation
                    bodyContent := cons.bodyContent }
    | none => info

end PWL.Transform.LambdaRestructure

export PWL.Transform.LambdaRestructure (
  findDirectReferences
  buildConsolidationChains
)
