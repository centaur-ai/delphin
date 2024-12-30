import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.ScopingCore

open MRS (Var EP)
open MM (Multimap)
open PWL.Transform (Formula Stats addStat getOrderedQuantArgs)
open HOF (lastTwoChars)
open InsertionSort
open BEq

structure EliminatedVars where
  vars : List Var
  deriving Inhabited

def EliminatedVars.empty : EliminatedVars := 
  EliminatedVars.mk []

def orderPredicateArgs (args : List (String × Var)) : List (String × Var) :=
  args.filter (fun a => a.1.startsWith "ARG") |> insertionSort

def isVarEliminated (ev : EliminatedVars) (v : Var) : Bool :=
  dbg_trace s!"isVarEliminated checking {v} against list {ev.vars}"
  ev.vars.contains v

def shouldEliminateHandle (hm : Multimap Var EP) (ev : EliminatedVars) (handle : Var) : Bool :=
  match hm.find? handle with
  | none => unreachable!  
  | some eps =>
    dbg_trace s!"shouldEliminateHandle checking handle {handle}"
    eps.any fun ep =>
      dbg_trace s!"  checking EP {ep}"
      ep.rargs.any fun (_, v) => 
        let isElim := isVarEliminated ev v
        dbg_trace s!"    arg {v} eliminated? {isElim}"
        isElim

def collectEliminatedVars (preds : List EP) : EliminatedVars :=
  dbg_trace "collectEliminatedVars starting"
  dbg_trace s!"Input predicates: {preds}"
  let result := preds.foldl (fun acc ep =>
    dbg_trace s!"Checking predicate: {ep.predicate}"
    dbg_trace s!"  lastTwoChars: {lastTwoChars ep.predicate}"
    dbg_trace s!"  args: {ep.rargs}"
    if lastTwoChars ep.predicate == "_q" then
      match ep.rargs with
      | ("ARG0", v) :: _ => 
        dbg_trace s!"  found quantifier {ep.predicate}, adding {v}"
        EliminatedVars.mk (v :: acc.vars)
      | other => 
        dbg_trace s!"  quantifier {ep.predicate} has unexpected args: {other}"
        acc
    else acc
  ) EliminatedVars.empty
  dbg_trace s!"collectEliminatedVars complete with {result.vars}"
  result

def isSimpleNamed (f : Formula) : Bool :=
  match f with 
  | Formula.atom ep => ep.predicate == "named" || ep.predicate == "_named"
  | _ => false

end PWL.Transform.ScopingCore

export PWL.Transform.ScopingCore (
  EliminatedVars 
  collectEliminatedVars 
  isVarEliminated 
  shouldEliminateHandle 
  isSimpleNamed
  orderPredicateArgs
)
