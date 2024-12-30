import Mrs.Basic
import Mrs.PwlTypes 
import Mrs.PwlTransformScopingCore
import Mrs.PwlTransformScoping
import Mrs.PwlTransformShared 
import Mrs.PwlTransformMinScoping
import Mrs.PwlTransformSerialize
import Mrs.PwlTransformNegationScopeRemoval
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform

open MRS (Var EP Constraint MRS)
open MM (Multimap)
open Lean (Format HashMap)
open InsertionSort
open HOF (lastTwoChars)
open PWL.Transform.ScopingCore (EliminatedVars isVarEliminated collectEliminatedVars shouldEliminateHandle)
open PWL.Transform.Scoping (processPredicates)
open PWL.Transform.MinScoping (ScopedEP analyzeFormula)

def updateHandleMap (preds : List EP) : Multimap Var EP :=
  let initial := preds.foldl (fun hm ep => hm.insert ep.label ep) Multimap.empty
  dbg_trace s!"updateHandleMap: Full handle map {if preds.length == initial.keys.length then "before" else "after"} phase1: {(initial.keys.map (fun h => h.sort.toString ++ toString h.id))}"
  initial

def phase0 (preds : List EP) : List EP :=
  let removeEventAnd (ep : EP) : Bool :=
    if ep.predicate == "and_c" || ep.predicate == "_and_c" then
      ep.rargs.all (fun arg => arg.2.sort == 'e')
    else
      false
  preds.filter (fun ep => !removeEventAnd ep)

def isCompoundInvolving (parent : Var) (pat : CompoundMatch) : Bool :=
  dbg_trace s!"Checking if compound involves parent {parent}"
  dbg_trace s!"  properQ1: {pat.properQ1}"
  dbg_trace s!"  properQ2: {pat.properQ2}"
  let isParentLabel := pat.properQ1.label == parent || pat.properQ2.label == parent
  let isParentBody := 
    (match pat.properQ1.rargs.find? (fun arg => arg.1 == "BODY") with
    | some (_, body) => body == parent
    | none => false) ||
    (match pat.properQ2.rargs.find? (fun arg => arg.1 == "BODY") with
    | some (_, body) => body == parent
    | none => false)
  dbg_trace s!"  isParentLabel: {isParentLabel}, isParentBody: {isParentBody}"
  isParentLabel || isParentBody

def getReferencedHandles (temps : List EP) : List Var :=
  let handles := temps.foldl (fun acc ep => 
    match ep.rargs with
    | ("X1", _) :: ("X2", _) :: ("A", a) :: ("B", b) :: _ => a :: b :: acc
    | _ => acc) []
  dbg_trace s!"Referenced handles from temps: {handles}"
  handles

def makeTemp (parent : Var) (ev : EliminatedVars) (pat : CompoundMatch) : Option EP :=
  dbg_trace s!"Making temp_compound_name with: pat.properQ1={pat.properQ1} pat.properQ2={pat.properQ2} pat.named1={pat.named1} pat.named2={pat.named2}"
  match pat.named1.carg, pat.named2.carg with 
  | some s1, some s2 =>
    let x1 := pat.properQ1.rargs.find? (fun arg => arg.1 == "ARG0")
    let x2 := pat.properQ2.rargs.find? (fun arg => arg.1 == "ARG0")
    let b1 := pat.properQ1.rargs.find? (fun arg => arg.1 == "BODY")
    let b2 := pat.properQ2.rargs.find? (fun arg => arg.1 == "BODY")
    match x1, x2, b1, b2 with
    | some (_, var1), some (_, var2), some (_, body1), some (_, body2) =>
      let label := if pat.properQ1.label == parent || pat.properQ2.label == parent 
                   then parent 
                   else pat.properQ2.label
      dbg_trace s!"Creating temp_compound_name with label: {label}"
      some (EP.mk "temp_compound_name" none label
        [("X1", var1), ("X2", var2), ("A", body1), ("B", body2)]
        (some ("\"" ++ removeExtraQuotes s1 ++ " " ++ removeExtraQuotes s2 ++ "\"")))
    | _, _, _, _ => none
  | _, _ => none

def shouldRemoveWithRefs (p : EP) (pat : CompoundMatch) (referencedHandles : List Var) : Bool :=
  if referencedHandles.contains p.label then
    dbg_trace s!"Keeping {p.label} due to reference"
    false
  else
    let remove := shouldRemove p pat
    dbg_trace s!"Removing {p.label}: {remove}"
    remove

def phase1 (parent : Var) (preds : List EP) (hm : Multimap Var EP) : (List EP × EliminatedVars × Var) :=
  dbg_trace s!"Phase 1 - Processing compound names with parent handle: {parent}"
  let compounds := preds.filter fun p => 
    p.predicate == "compound" || p.predicate == "_compound"
  let patterns := compounds.filterMap (fun c => getCompoundPattern preds c hm)
  let temps := patterns.filterMap (makeTemp parent EliminatedVars.empty)
  let referencedHandles := getReferencedHandles temps
  let labelsToRemove := patterns.foldl (fun acc pat =>
    [pat.compound.label, pat.properQ1.label, pat.properQ2.label, 
     pat.named1.label, pat.named2.label] ++ acc) []
  let rootInvolvedPatterns := patterns.filter (isCompoundInvolving parent)
  let eliminatedVars := collectEliminatedVars $
    patterns.filter (fun p => temps.any (fun t => t.predicate == "temp_compound_name"))
    |>.map (fun p => p.compound)
  let remaining := preds.filter fun pred =>
    !labelsToRemove.contains pred.label &&
    !(referencedHandles.contains pred.label && 
      (pred.predicate == "named" || pred.predicate == "_named"))
  let newRoot := 
    if rootInvolvedPatterns.isEmpty then parent
    else match temps.find? (fun t => t.label == parent) with
         | some temp => temp.label
         | none => parent
  (remaining ++ temps, eliminatedVars, newRoot)

def phase2 (parent : Var) (handle : Var) (preds : List EP) (ev : EliminatedVars) (hm : Multimap Var EP) : Option Formula :=
  dbg_trace s!"Phase 2 - Rewriting temp compounds for handle: {handle}"
  dbg_trace s!"  parent handle was: {parent}"
  match hm.find? handle with 
  | none => 
    dbg_trace "No predicates found for handle"
    unreachable!
  | some rootPreds => 
    let substitutions := preds.foldl (fun acc ep =>
      if ep.predicate == "temp_compound_name" then
        match (getArg ep "X1", getArg ep "X2") with
        | (some x1, some x2) => (x2, x1) :: acc
        | _ => acc
      else acc) []
    let emptyStats : Stats := default
    let (result, _) := processPredicates handle rootPreds [] hm emptyStats ev
    match result with
    | none => none 
    | some formula =>
      let substituted := substitutions.foldl (fun f (old, new) => f.substitute old new) formula
      some substituted
      |>.map Formula.removeEmptyConj

def phase3 (f : Formula) : Formula := 
  dbg_trace "Phase 3 - Converting X2 to X1"
  f

def phase4 (f : Formula) : Formula :=
  dbg_trace "Phase 4 - Minimum scoping"
  minimizeScoping f

def phase5 := PWL.Transform.NegationScopeRemoval.simplifyNegation

def phase6 (f : Formula) : String :=
  dbg_trace "Phase 6 - Serializing to PWL format"
  formatAsPWL f none

def transform (handle : Var) (preds : List EP) (hm : Multimap Var EP) : String :=
  let msg := s!"Transform - Starting with handle {handle}\nPreds count: {preds.length}\nHandle map size: {hm.keys.length}\nHandle map contents: {(hm.keys.map fun k => (k, hm.find? k))}"
  dbg_trace msg

  let filteredPreds := phase0 preds
  let (p1preds, ev, newRoot) := phase1 handle filteredPreds hm
  dbg_trace "After phase1, updating handle map with temp compounds" 
  let newHm := updateHandleMap p1preds

  match phase2 handle newRoot p1preds ev newHm with
  | none => "!!! NO FORMULA GENERATED !!!"
  | some formula =>
      let substituted := phase3 formula
      let minScoped := phase4 substituted
      let negSimplified := phase5 minScoped
      phase6 negSimplified

end PWL.Transform

export PWL.Transform (transform)
