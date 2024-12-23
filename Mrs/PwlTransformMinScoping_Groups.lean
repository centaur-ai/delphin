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
  (match (ep1.rargs.map (·.2), ep2.rargs.map (·.2)) with
  | (vars1, vars2) =>
    dbg_trace s!"Compare vars: {ep1.predicate}->{vars1} with {ep2.predicate}->{vars2}"
    vars1.any (fun v1 => vars2.any (fun v2 => v1 == v2)))

def buildPredicateGroups (preds : List EP) (level : Nat) : List PredicateGroup :=
  let buildGroup (pred : EP) (remaining : List EP) : PredicateGroup × List EP :=
    (match (remaining.filter (sharesVariables pred), 
           remaining.filter (fun p => !(sharesVariables pred p))) with
    | (related, newRemaining) =>
      dbg_trace s!"Group for {pred.predicate} level {level}:
        Related: {related.map (·.predicate)}
        Remaining: {newRemaining.map (·.predicate)}"
      let allVars := (pred :: related).foldl (fun acc ep =>
        acc ++ ep.rargs.map (·.2)) []
      ({ mainPred := pred, 
         relatedPreds := related,
         requiredVars := allVars.eraseDups },
       newRemaining))

  let rec buildGroups (ps : List EP) : List PredicateGroup :=
    match ps with
    | [] => []
    | p :: rest => 
      let (group, remaining) := buildGroup p rest
      group :: buildGroups remaining
      
  (match buildGroups preds with
  | groups =>
    dbg_trace s!"Level {level} groups: {groups.map (fun g => 
      (g.mainPred.predicate, g.relatedPreds.map (·.predicate), g.requiredVars))}"
    groups)

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (PredicateGroup sharesVariables buildPredicateGroups)
