import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS
open InsertionSort
open PWL.Transform
open Lean (HashMap)
open BEq

structure PredicateGroup where
  mainPred : EP 
  relatedPreds : List EP
  requiredVars : List Var
  deriving Inhabited

instance : ToString PredicateGroup where
  toString g := s!"Group({g.mainPred.predicate} + {g.relatedPreds.length} related)"

def sharesVariables (ep1 ep2 : EP) : Bool := 
  let vars1 := ep1.rargs.map (·.2)
  let vars2 := ep2.rargs.map (·.2)
  dbg_trace s!"Compare vars: {ep1.predicate}->{vars1} with {ep2.predicate}->{vars2}"
  vars1.any (fun v1 => vars2.any (fun v2 => v1 == v2))

def buildPredicateGroup (pred : EP) (remaining : List EP) :
    PredicateGroup × List EP :=
  let (related, newRemaining) := 
    remaining.partition (fun p => sharesVariables pred p)
  dbg_trace s!"Group for {pred.predicate}:
    Related: {related.map (·.predicate)}
    Remaining: {newRemaining.map (·.predicate)}"
  let allVars := (pred :: related).foldl (fun acc ep =>
    acc ++ ep.rargs.map (·.2)) []
  ({mainPred := pred, 
    relatedPreds := related,
    requiredVars := allVars.eraseDups},
    newRemaining)

partial def buildPredicateGroups (preds : List EP) (level : Nat) : List (List EP) :=
  let rec buildGroups (ps : List EP) (acc : List (List EP)) (size : Nat) : List (List EP) :=
    match ps with
    | [] => acc 
    | p :: rest => 
      if size = 0 then acc else
      let (group, remaining) := buildPredicateGroup p rest
      buildGroups remaining ([group.mainPred] :: group.relatedPreds :: acc) (size - 1)
  
  let result := buildGroups preds [] preds.length
  dbg_trace s!"Level {level} groups: {result}"
  result

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (PredicateGroup sharesVariables buildPredicateGroups)
