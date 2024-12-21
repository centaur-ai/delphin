import Mrs.Basic
import Mrs.PwlTypes 
import Mrs.PwlTransformScoping
import Mrs.PwlTransformShared 
import Mrs.PwlTransformMinScoping
import Mrs.PwlTransformSerialize
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform

open MRS (Var EP Constraint MRS)
open MM (Multimap)
open Lean (Format HashMap)
open InsertionSort
open HOF (lastTwoChars)
open PWL.Transform.Scoping (EliminatedVars isVarEliminated collectEliminatedVars shouldEliminateHandle processPredicates)

def makeTemp (parent : Var) (ev : EliminatedVars) (pat : CompoundMatch) : Option EP :=
  dbg_trace ("Making temp_compound_name with: pat.properQ1=" ++ toString pat.properQ1 ++
             " pat.properQ2=" ++ toString pat.properQ2 ++
             " pat.named1=" ++ toString pat.named1 ++
             " pat.named2=" ++ toString pat.named2)
  match pat.named1.carg, pat.named2.carg with
  | some s1, some s2 =>
    let x1 := pat.properQ1.rargs.find? (fun arg => arg.1 == "ARG0")
    let x2 := pat.properQ2.rargs.find? (fun arg => arg.1 == "ARG0")
    let b1 := pat.properQ1.rargs.find? (fun arg => arg.1 == "BODY")
    let b2 := pat.properQ2.rargs.find? (fun arg => arg.1 == "BODY")
    match x1, x2, b1, b2 with
    | some (_, var1), some (_, var2), some (_, body1), some (_, body2) =>
      -- Use parent handle as label if this involves root
      let label := if pat.properQ1.label == parent || pat.properQ2.label == parent 
                   then parent 
                   else pat.properQ2.label
      dbg_trace ("Creating temp_compound_name with label: " ++ toString label)
      some (EP.mk "temp_compound_name" none label
        [("X1", var1), ("X2", var2), ("A", body1), ("B", body2)]
        (some ("\"" ++ removeExtraQuotes s1 ++ " " ++ removeExtraQuotes s2 ++ "\"")))
    | _, _, _, _ => none
  | _, _ => none

def isCompoundInvolving (parent : Var) (pat : CompoundMatch) : Bool :=
  dbg_trace ("Checking if compound involves parent " ++ toString parent)
  dbg_trace ("  properQ1: " ++ toString pat.properQ1)
  dbg_trace ("  properQ2: " ++ toString pat.properQ2)
  let isParentLabel := pat.properQ1.label == parent || pat.properQ2.label == parent
  let isParentBody := 
    (match pat.properQ1.rargs.find? (fun arg => arg.1 == "BODY") with
    | some (_, body) => body == parent
    | none => false) ||
    (match pat.properQ2.rargs.find? (fun arg => arg.1 == "BODY") with
    | some (_, body) => body == parent
    | none => false)
  dbg_trace ("  isParentLabel: " ++ toString isParentLabel ++ ", isParentBody: " ++ toString isParentBody)
  isParentLabel || isParentBody

def getReferencedHandles (temps : List EP) : List Var :=
  let handles := temps.foldl (fun acc ep => 
    match ep.rargs with
    | ("X1", _) :: ("X2", _) :: ("A", a) :: ("B", b) :: _ => a :: b :: acc
    | _ => acc) []
  dbg_trace ("Referenced handles from temps: " ++ toString handles)
  handles

def shouldRemoveWithRefs (p : EP) (pat : CompoundMatch) (referencedHandles : List Var) : Bool :=
  -- Keep predicates whose handles are referenced by temp_compound_name
  if referencedHandles.contains p.label then
    dbg_trace ("Keeping " ++ toString p.label ++ " due to reference")
    false
  else
    let remove := shouldRemove p pat
    dbg_trace ("Removing " ++ toString p.label ++ ": " ++ toString remove)
    remove

def phase1 (parent : Var) (preds : List EP) (hm : Multimap Var EP) : (List EP × EliminatedVars × Var) :=
  dbg_trace ("phase1 starting with parent handle: " ++ toString parent)
  dbg_trace ("Initial predicates: " ++ toString preds)
  
  let compounds := preds.filter fun p => 
    p.predicate == "compound" || p.predicate == "_compound"
  dbg_trace ("Found compounds: " ++ toString compounds)
  
  let patterns := compounds.filterMap (fun c => getCompoundPattern preds c hm)
  dbg_trace ("Found patterns: " ++ toString patterns)
  dbg_trace ("Found pattern handles: " ++ toString (patterns.map (fun p => p.compound.label)))

  let temps := patterns.filterMap (makeTemp parent EliminatedVars.empty)
  dbg_trace ("Created temp compounds: " ++ toString temps)
  
  -- Get all handles referenced by temp compounds
  let referencedHandles := getReferencedHandles temps
  dbg_trace ("Referenced handles: " ++ toString referencedHandles)

  let rootInvolvedPatterns := patterns.filter (isCompoundInvolving parent)
  dbg_trace ("Patterns involving root: " ++ toString rootInvolvedPatterns)

  let eliminatedVars := collectEliminatedVars $
    patterns.filter (fun p => temps.any (fun t => t.predicate == "temp_compound_name"))
    |>.map (fun p => p.compound)
  
  -- Keep predicates at referenced handles
  let remaining := preds.filter fun pred =>
    not (patterns.any (fun pat => shouldRemoveWithRefs pred pat referencedHandles))
  
  dbg_trace ("Remaining predicates: " ++ toString remaining)
  
  let newRoot := 
    if rootInvolvedPatterns.isEmpty then
      dbg_trace ("Keeping root as " ++ toString parent)
      parent
    else
      match temps.find? (fun t => t.label == parent) with
      | some temp =>
        dbg_trace ("Found new root temp_compound_name: " ++ toString temp)
        temp.label
      | none =>
        dbg_trace ("No matching temp_compound_name for root, keeping " ++ toString parent)
        parent

  dbg_trace ("Final root handle: " ++ toString newRoot)
  dbg_trace ("Final predicates: " ++ toString (remaining ++ temps))

  (remaining ++ temps, eliminatedVars, newRoot)

def phase2 (parent : Var) (handle : Var) (preds : List EP) (ev : EliminatedVars) (hm : Multimap Var EP) : Option Formula :=
  dbg_trace ("phase2 entry - processing handle: " ++ toString handle)
  dbg_trace ("  parent handle was: " ++ toString parent)
  
  let allHandleRefs := preds.foldl (fun acc ep => 
    ep.rargs.foldl (fun acc2 (name, v) => if v.sort == 'h' then (ep.label, name, v) :: acc2 else acc2) acc) []
  dbg_trace ("  all handle references in predicates: " ++ toString allHandleRefs)
  
  match hm.find? handle with 
  | none => 
    dbg_trace "No predicates found for handle"
    unreachable!
  | some rootPreds => 
    dbg_trace ("phase2 starting at handle " ++ toString handle)
    dbg_trace ("  root predicates: " ++ toString rootPreds)
    
    dbg_trace ("  all available predicates: " ++ toString preds)
    
    let referencingPreds := preds.filter (fun p => p.rargs.any (fun (_, v) => v == handle))
    dbg_trace ("  predicates referencing this handle: " ++ toString referencingPreds)
    
    let labeledPreds := preds.filter (fun p => p.label == handle)
    dbg_trace ("  predicates with this handle as label: " ++ toString labeledPreds)
    
    let substitutions := preds.foldl (fun acc ep =>
      if ep.predicate == "temp_compound_name" then
        match (getArg ep "X1", getArg ep "X2") with
        | (some x1, some x2) => (x2, x1) :: acc
        | _ => acc
      else acc) []
    dbg_trace ("Collected substitutions: " ++ toString substitutions)

    let emptyStats : Stats := default
    let (result, _) := processPredicates handle rootPreds [] hm emptyStats ev
    match result with
    | none => 
      dbg_trace "processPredicates returned none"
      none
    | some formula =>
      dbg_trace ("processPredicates returned formula: " ++ toString formula)
      let substituted := substitutions.foldl (fun f (old, new) => f.substitute old new) formula
      dbg_trace ("After substitutions: " ++ toString substituted)
      some substituted
      |>.map Formula.removeEmptyConj

def phase3 (f : Formula) : Formula :=
  dbg_trace "Starting phase3"
  dbg_trace s!"Phase3 input formula: {f}"
  let minScoped := minimizeScoping f
  dbg_trace s!"Phase3 output formula: {minScoped}" 
  minScoped

def phase4 (f : Formula) : String :=
  formatAsPWL f none

def updateHandleMap (preds : List EP) : Multimap Var EP :=
  let initial := preds.foldl (fun hm ep => hm.insert ep.label ep) Multimap.empty
  dbg_trace ("updateHandleMap: Full handle map " ++ 
    (if preds.length == initial.keys.length then "before" else "after") ++
    " phase1: " ++ toString (initial.keys.map (fun h => h.sort.toString ++ toString h.id)))
  initial

def transform (handle : Var) (preds : List EP) (hm : Multimap Var EP) : String :=
  let msg := "Transform - Starting with handle " ++ toString handle ++
             "\nPreds count: " ++ toString preds.length ++
             "\nHandle map size: " ++ toString hm.keys.length ++
             "\nHandle map contents: " ++ toString (hm.keys.map (fun k => (k, hm.find? k)))
  dbg_trace msg
  
  let (p1preds, ev, newRoot) := phase1 handle preds hm
  dbg_trace "After phase1, updating handle map with temp compounds"
  let newHm := updateHandleMap p1preds 
  dbg_trace ("  new handle map size: " ++ toString newHm.keys.length)
  
  match phase2 handle newRoot p1preds ev newHm with
  | none => "!!! NO FORMULA GENERATED !!!"
  | some formula => 
      dbg_trace "Phase2 output formula:"
      dbg_trace s!"{formula}"
      let minScoped := phase3 formula
      dbg_trace "After phase3:"
      dbg_trace s!"{minScoped}"
      phase4 minScoped

end PWL.Transform

export PWL.Transform (transform)
