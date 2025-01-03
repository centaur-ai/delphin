import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Types
import Mrs.PwlTransformMinScoping_Core
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (EP Var)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

def extractGuardedBodies (f : Formula) : (List Formula × List Formula × List Formula) :=
  dbg_trace s!"PWL: extractGuardedBodies input formula:\n{f}"
  match f with
  | Formula.conj fs =>
    dbg_trace s!"PWL: examining {fs.length} conjuncts"
    let rstrGuards := fs.filter fun f => match f with
      | Formula.scope [] (some "rstr_guard") _ => true
      | _ => false
    let bodyGuards := fs.filter fun f => match f with
      | Formula.scope [] (some "body_guard") _ => true
      | _ => false
    let otherFormulas := fs.filter fun f => match f with
      | Formula.scope [] (some "rstr_guard") _ => false
      | Formula.scope [] (some "body_guard") _ => false
      | _ => true

    let rstrBodies := rstrGuards.map fun f => match f with
      | Formula.scope _ _ inner => match inner with
        | Formula.atom ep => [Formula.atom ep]
        | Formula.conj innerFs => innerFs
        | _ => []
      | _ => []
    let rstrFormulas := rstrBodies.foldl (· ++ ·) []

    let bodyBodies := bodyGuards.map fun f => match f with
      | Formula.scope _ _ inner => match inner with
        | Formula.atom ep => [Formula.atom ep]
        | Formula.conj innerFs => innerFs
        | _ => []
      | _ => []
    let bodyFormulas := bodyBodies.foldl (· ++ ·) []

    dbg_trace s!"PWL: found {rstrFormulas.length} RSTR formulas"
    dbg_trace s!"PWL: found {bodyFormulas.length} BODY formulas" 
    dbg_trace s!"PWL: found {otherFormulas.length} other formulas"

    (rstrFormulas, bodyFormulas, otherFormulas)
  | _ => 
    dbg_trace s!"PWL: no conjunction found in:\n{f}"
    ([], [], [f])

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (extractGuardedBodies)
