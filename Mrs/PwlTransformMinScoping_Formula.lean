import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Mrs.PwlTransformMinScoping_Analysis
import Mrs.PwlTransformMinScoping_Events
import Mrs.PwlTransformSerializeTheQ
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (EP Var)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

def buildScopedFormula (scope : ScopeInfo) (inner : Formula) : Formula :=
  dbg_trace s!"MINSCOPE:buildScopedFormula for {scope.predicate} type={toString scope.scopeType}"
  match scope.scopeType with
  | ScopeType.RstrGuard => 
    dbg_trace "MINSCOPE:  Creating RSTR guard scope without variables"
    let result := Formula.scope [] (some "rstr_guard") inner
    dbg_trace s!"MINSCOPE:  RSTR guard formula created:\n{result}"
    result
  | _ =>
    dbg_trace s!"MINSCOPE:  Creating regular scope with vars={scope.boundVars}"
    let result := Formula.scope scope.boundVars (some scope.predicate) inner
    dbg_trace s!"MINSCOPE:  Regular scope formula created:\n{result}"
    result

def buildEventGroupFormula (group : List EP) (inner : Formula) (scopedEvents : List Var) : Formula :=
  dbg_trace s!"MINSCOPE:buildEventGroupFormula starting with {group.length} predicates:\n{group.map (·.predicate)}"
  dbg_trace s!"MINSCOPE:  Already scoped events: {scopedEvents}"
  
  let eventVars := group.foldl (fun acc ep => 
    let newVars := getEventVars ep |>.filter (fun v => !scopedEvents.contains v)
    dbg_trace s!"MINSCOPE:  Getting events from {ep.predicate}: new={newVars}"
    (acc ++ newVars).eraseDups) []
    
  match eventVars with
  | [] => 
    dbg_trace "MINSCOPE:  No new events - returning plain conjunction"
    let result := Formula.conj (group.map Formula.atom ++ [inner])
    dbg_trace s!"MINSCOPE:  Plain conjunction result:\n{result}"
    result
  | _ => 
    dbg_trace s!"MINSCOPE:  Creating event scope with vars: {eventVars}"
    let result := Formula.scope eventVars none 
      (Formula.conj (group.map Formula.atom ++ [inner]))
    dbg_trace s!"MINSCOPE:  Event scope result:\n{result}"
    result

def buildEventConj (groups : List (List EP)) (inner : Formula) (scopedEvents : List Var := []) : Formula :=
  dbg_trace s!"MINSCOPE:buildEventConj processing {groups.length} groups:"
  dbg_trace s!"MINSCOPE:  Groups: {groups.map (fun g => g.map (·.predicate))}"
  dbg_trace s!"MINSCOPE:  Already scoped events: {scopedEvents}"
  match groups with
  | [] => 
    dbg_trace "MINSCOPE:  No groups - returning inner formula"
    inner
  | g :: gs => 
    dbg_trace s!"MINSCOPE:  Processing group {g.map (·.predicate)}"
    let result := buildEventConj gs inner scopedEvents
    -- Get all events from this group
    let groupEvents := g.foldl (fun acc ep =>
      (acc ++ getEventVars ep).eraseDups) []
    -- Only scope events not already scoped
    let newEvents := groupEvents.filter (fun v => !scopedEvents.contains v)
    if newEvents.isEmpty then
      dbg_trace "MINSCOPE:  No new events to scope - returning conjunction"
      Formula.conj (g.map Formula.atom ++ [result])
    else  
      dbg_trace s!"MINSCOPE:  Creating scope for new events: {newEvents}"
      Formula.scope newEvents none
        (Formula.conj (g.map Formula.atom ++ [result]))

partial def buildFormula (scopes : List ScopeInfo) (preds : List ScopedEP) (scopedEvents : List Var) : Formula :=
  let makeIndent (n : Nat) := String.mk (List.replicate n ' ')

  let rec dumpFormula : Formula → Nat → String
    | Formula.atom ep, indent => "\n" ++ (makeIndent indent) ++ s!"Atom: {ep.predicate}"
    | Formula.scope vars (some name) inner, indent => 
      "\n" ++ (makeIndent indent) ++ s!"Scope [{name}] vars={vars}:" ++ 
      dumpFormula inner (indent + 2)
    | Formula.scope vars none inner, indent => 
      "\n" ++ (makeIndent indent) ++ s!"Scope [unnamed] vars={vars}:" ++ 
      dumpFormula inner (indent + 2)
    | Formula.conj fs, indent =>
      "\n" ++ (makeIndent indent) ++ "Conj:" ++
      (fs.foldl (fun acc f => acc ++ dumpFormula f (indent + 2)) "")

  -- Main buildFormula logic
  dbg_trace s!"\nMINSCOPE:buildFormula entry"
  dbg_trace s!"  Input scopes: {scopes.map (fun s => s!"{s.predicate}/{s.scopeType}")}"
  dbg_trace s!"  Input preds before filtering: {preds.map (fun p => s!"{p.predicate.predicate}[scope={p.scope}]")}"
  dbg_trace s!"  Scoped events: {scopedEvents}"

  (match scopes, preds with
  | [], [] => 
    dbg_trace "MINSCOPE:  Empty scopes and preds - returning empty conjunction"
    Formula.conj []
    
  | [], remaining => 
    dbg_trace s!"MINSCOPE:  No scopes but {remaining.length} predicates - grouping by events"
    let groups := findEventGroups (remaining.map (·.predicate))
    dbg_trace s!"MINSCOPE:  Found event groups: {groups.map (fun g => g.map (·.predicate))}"
    buildEventConj groups (Formula.conj []) scopedEvents
    
  | scope :: restScopes, preds =>
    dbg_trace s!"MINSCOPE:  Processing scope {scope.predicate} [{scope.scopeType}]"
    dbg_trace s!"  Raw predicates before scope processing: {preds.map (fun p => s!"{p.predicate.predicate}[scope={p.scope}]")}"
    
    if scope.scopeType == ScopeType.Definite && 
       (scope.predicate == "the_q" || scope.predicate == "_the_q") then
      dbg_trace "MINSCOPE:  THE_Q scope detected"
      
      (match scope.boundVars.head? with
      | none => 
        dbg_trace "MINSCOPE:    ERROR: THE_Q scope has no bound variables"
        unreachable!
      | some theqVar =>
        dbg_trace s!"MINSCOPE:    THE_Q bound var: {theqVar}"
        dbg_trace s!"MINSCOPE:    Starting partition check on predicates: {preds.map (fun p => s!"{p.predicate.predicate}[scope={p.scope}]")}"
        let partition := preds.partition (fun ep =>
          dbg_trace s!"MINSCOPE:      Testing partition for {ep.predicate.predicate}[scope={ep.scope}]"
          (match ep.scope with
          | none => 
            dbg_trace s!"MINSCOPE:      Pred {ep.predicate.predicate} - no scope, not RSTR"
            false
          | some scopeVar =>
            let isRstr := scopeVar.sort == 'r' && scopeVar.id == theqVar.id
            dbg_trace s!"MINSCOPE:      Pred {ep.predicate.predicate} - scope={scopeVar}, theqVar={theqVar}, isRstr={isRstr}"
            isRstr))
            
        dbg_trace s!"MINSCOPE:    RSTR preds: {partition.1.map (·.predicate.predicate)}"
        dbg_trace s!"MINSCOPE:    BODY preds: {partition.2.map (·.predicate.predicate)}"
        
        let rstrFormula := Formula.scope [] (some "rstr_guard") 
          (Formula.conj (partition.1.map (·.predicate) |>.map Formula.atom))
        dbg_trace s!"MINSCOPE:    RSTR formula:\n{dumpFormula rstrFormula 6}"
        
        let bodyFormula := buildFormula restScopes partition.2 scopedEvents
        dbg_trace s!"MINSCOPE:    BODY formula:\n{dumpFormula bodyFormula 6}"
        
        let result := buildScopedFormula scope (Formula.conj [rstrFormula, bodyFormula])
        dbg_trace s!"MINSCOPE:    Final THE_Q result:\n{dumpFormula result 6}"
        result)

    else
      dbg_trace "MINSCOPE:  Regular scope processing"
      dbg_trace s!"MINSCOPE:    Finding predicates for this scope"
      
      let (hereEps, otherEps) := preds.partition (fun ep => 
        match determineMinScope ep (scope :: restScopes) with
        | some s =>
          let isHere := s == scope
          dbg_trace s!"MINSCOPE:      Pred {ep.predicate.predicate} - can lift to {s.predicate}, here?={isHere}"
          isHere
        | none =>
          dbg_trace s!"MINSCOPE:      Pred {ep.predicate.predicate} - cannot lift"
          false)
      
      dbg_trace s!"MINSCOPE:    Here preds: {hereEps.map (·.predicate.predicate)}"
      dbg_trace s!"MINSCOPE:    Other preds: {otherEps.map (·.predicate.predicate)}"
      
      let groups := findEventGroups (hereEps.map (·.predicate))
      dbg_trace s!"MINSCOPE:    Event groups at this level: {groups.map (fun g => g.map (·.predicate))}"
      
      let groupEvents := groups.foldl (fun acc g => 
        let newEvents := (g.foldl (fun acc2 ep => acc2 ++ getEventVars ep) [])
        dbg_trace s!"MINSCOPE:      Group events: {newEvents}"
        (acc ++ newEvents).eraseDups) []
      dbg_trace s!"MINSCOPE:    All group events: {groupEvents}"
      
      let newScopedEvents := scopedEvents ++ groupEvents
      dbg_trace s!"MINSCOPE:    Combined scoped events: {newScopedEvents}"
      
      let innerFormula := buildFormula restScopes otherEps newScopedEvents
      dbg_trace s!"MINSCOPE:    Inner formula:\n{dumpFormula innerFormula 6}"
      
      let eventFormula := buildEventConj groups innerFormula scopedEvents
      dbg_trace s!"MINSCOPE:    Event formula:\n{dumpFormula eventFormula 6}"
      
      let result := buildScopedFormula scope eventFormula
      dbg_trace s!"MINSCOPE:  Regular scope result:\n{dumpFormula result 4}"
      result)

partial def minimizeScoping (f : Formula) : Formula := 
  dbg_trace "MINSCOPE:minimizeScoping starting"
  let (scopes, preds) := analyzeFormula f
  
  let result := buildFormula scopes preds []
  dbg_trace s!"MINSCOPE:minimizeScoping complete\n  result={result}"
  result

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (buildFormula buildEventConj buildEventGroupFormula buildScopedFormula minimizeScoping)
