import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Types
import Mrs.PwlTransformMinScoping_Variables
import Mrs.PwlTransformFormat
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

def containsEP (preds : List ScopedEP) (ep : EP) : Bool :=
  preds.any fun p => ep == p.predicate

def getRstrHandle (f : Formula) : Option Var :=
  match f with
  | Formula.atom ep =>
    ep.rargs.find? (fun arg => arg.1 == "RSTR")
    |>.map (fun arg => arg.2)
  | _ => none

def isRstrPredicate (ep : EP) : Bool :=
  let result := ep.rargs.any (fun arg => arg.1 == "RSTR")
  dbg_trace s!"RSTR check {ep.predicate}: args={(ep.rargs.map (fun arg => s!"{arg.1}={arg.2}"))} found={result}"
  result

partial def hasRstrPredicate (f : Formula) : Bool :=
  match f with
  | Formula.atom ep => isRstrPredicate ep
  | Formula.conj fs => fs.any hasRstrPredicate
  | Formula.scope _ _ inner => hasRstrPredicate inner

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (
  containsEP
  getRstrHandle
  isRstrPredicate
  hasRstrPredicate
)
