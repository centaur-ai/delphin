import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Mrs.PwlTransformMinScoping_Formula
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS
open InsertionSort
open PWL.Transform
open Lean (HashMap)
open BEq

mutual 
  partial def minimizeScopeRegion (f : Formula) (level : Nat := 0) : Formula :=
    let indent := String.mk (List.replicate (level * 2) ' ')
    match f with
    | Formula.atom _ => f 
    | Formula.conj fs =>
      dbg_trace s!"{indent}### Processing conjunction at level {level}"
      let preds := getPredicatesFromFormula f level
      dbg_trace s!"{indent}Found predicates: {preds}"
      buildMinimalFormula preds f [] level
    | Formula.scope vars quant inner =>
      dbg_trace s!"{indent}Processing scope vars={vars} quant={quant} at level {level}"
      dbg_trace s!"{indent}Variables being scoped: {toString vars}"
      let result := Formula.scope vars quant (minimizeScopeRegion inner (level + 1))
      dbg_trace s!"{indent}Completed scope processing at level {level}"
      dbg_trace s!"{indent}Resulting formula: {toString result}"
      result
end

partial def minimizeScoping (f : Formula) : Formula := 
  dbg_trace "Starting minimizeScoping"
  let result := minimizeScopeRegion f
  dbg_trace s!"minimizeScoping complete. Result:\n{result}"
  result

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (minimizeScoping)
