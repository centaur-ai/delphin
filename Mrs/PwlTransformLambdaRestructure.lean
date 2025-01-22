import Mrs.Basic
import Mrs.PwlTypes 
import Mrs.PwlTransformShared
import Mrs.PwlTransformScopingCore
import Mrs.PwlTransformLambdaRestructure_Types
import Mrs.PwlTransformLambdaRestructure_Chains
import Mrs.PwlTransformLambdaRestructure_TreeOps
import Mrs.PwlTransformLambdaRestructure_ScopeAdjustment
import Mrs.Hof
import Util.InsertionSort
import Lean.Data.RBTree

namespace PWL.Transform.LambdaRestructure

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open HOF
open Lean

/-- Main entry point for lambda restructuring -/
def restructureLambdas (f : Formula) (lambdaVars : RBTree Var compare) : Formula :=
  dbg_trace "RESTRUCTURE: Starting lambda restructuring"
  dbg_trace s!"RESTRUCTURE: Initial formula {f}"
  
  -- Phase 1: Identify and consolidate lambdas
  let infos := buildConsolidationChains f
  dbg_trace s!"RESTRUCTURE: Got consolidation infos {infos}"

  -- Extract obsolete vars for removal
  let obsoleteVars := infos.filter (·.status == LambdaStatus.Obsolete)
  dbg_trace s!"RESTRUCTURE: Obsolete lambdas {obsoleteVars}"
  
  -- Remove obsolete vars first
  let baseFml := removeObsoleteLambdas f (obsoleteVars.map (·.sourceVar))
  dbg_trace "RESTRUCTURE: Removed old lambdas"
  dbg_trace s!"RESTRUCTURE: After removal, structure is:\n{baseFml}"

  -- Phase 2: Build consolidated versions
  let withConsolidated := infos.foldl (fun acc info =>
    if info.status == LambdaStatus.KeepScope then
      dbg_trace s!"RESTRUCTURE: Processing kept lambda {info.sourceVar}"
      insertConsolidatedAt acc info.sourceVar info.targetVars (obsoleteVars.map (·.sourceVar))
    else
      dbg_trace s!"RESTRUCTURE: Skipping lambda {info.sourceVar}"
      acc) baseFml
      
  dbg_trace s!"RESTRUCTURE: After consolidation {withConsolidated}"

  dbg_trace (formatFragmentPaths withConsolidated)

  -- Phase 3: Analyze and adjust scoping
  let scopes := analyzeScopedVars withConsolidated
  dbg_trace s!"RESTRUCTURE: Analyzed scopes {scopes}"

  let moves := planMoves withConsolidated scopes
  dbg_trace s!"RESTRUCTURE: Planned moves {moves}"

  let final := adjustScopes withConsolidated moves 
  dbg_trace s!"RESTRUCTURE: Final result {final}"

  final

end PWL.Transform.LambdaRestructure

export PWL.Transform.LambdaRestructure (restructureLambdas)
