import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Mrs.PwlTransformMinScoping_Analysis
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (Var EP Constraint MRS)
open InsertionSort
open PWL.Transform
open Lean (HashMap)
open BEq

instance : BEq EP where 
  beq ep1 ep2 := ep1.predicate == ep2.predicate && 
                 ep1.rargs.length == ep2.rargs.length &&
                 ep1.link == ep2.link &&
                 ep1.label == ep2.label &&
                 ep1.carg == ep2.carg &&
                 (ep1.rargs.zip ep2.rargs).all (fun (a, b) => a == b)

def getEventVars (ep : EP) : List Var :=
  let vars := ep.rargs.filter (fun arg => arg.2.sort == 'e' || arg.2.sort == 'i')
    |>.map (·.2)
  dbg_trace s!"getEventVars for {ep.predicate}: {vars}"
  vars

def getNonEventVars (ep : EP) : List Var :=
  ep.rargs.filter (fun arg => arg.2.sort == 'x')
    |>.map (·.2)

def getVarDeps (ep : EP) : List Var :=
  ep.rargs.filter (fun arg => arg.2.sort == 'x' || arg.2.sort == 'e' || arg.2.sort == 'i')
    |>.map (·.2)

structure ScopedEP where
  predicate : EP
  scope : Option Var
  deriving Inhabited, BEq

instance : BEq ScopeInfo where
  beq si1 si2 := si1.predicate == si2.predicate && 
                 si1.boundVars == si1.boundVars && 
                 si1.scopeType == si2.scopeType &&
                 si1.negVar == si2.negVar

partial def findEventGroups (preds : List EP) : List (List EP) :=
  dbg_trace s!"findEventGroups starting with {preds.length} predicates"
  -- First find ALL predicates with events or implicit vars
  let allEventPreds := preds.filter (fun p => 
    let evs := getEventVars p
    dbg_trace s!"Checking events for {p.predicate}: {evs}"
    !evs.isEmpty)
  dbg_trace s!"All event-containing predicates: {allEventPreds.map (·.predicate)}"

  -- Pass allEventPreds as parameter to findConnected
  let rec findConnected (pred : EP) (seen : List EP) : List EP :=
    let myEvents := getEventVars pred
    dbg_trace s!"Finding connected for {pred.predicate} with events {myEvents}"

    let directlyConnected := allEventPreds.filter fun p => 
      if seen.contains p then 
        dbg_trace s!"  Skipping {p.predicate} - already seen"
        false 
      else
        let theirEvents := getEventVars p
        let eventMatches := myEvents.map fun myE => 
          theirEvents.any fun theirE => 
            let isMatch := myE == theirE
            dbg_trace s!"    Comparing events {myE} == {theirE}: {isMatch}"
            isMatch
        let isConnected := eventMatches.any id
        dbg_trace s!"  Checking {p.predicate} with events {theirEvents}, has matches {eventMatches}, connected? {isConnected}"
        isConnected

    let seenWithMe := pred :: seen
    dbg_trace s!"  Directly connected: {directlyConnected.map (·.predicate)}"
    dbg_trace s!"  Already seen: {seenWithMe.map (·.predicate)}"
    
    let nextGroups := directlyConnected.foldl (fun acc p =>
      if acc.contains p then acc
      else findConnected p acc
    ) seenWithMe

    dbg_trace s!"  Returning group: {nextGroups.map (·.predicate)}"
    nextGroups

  let rec findAllGroups (remaining : List EP) (processedGroups : List (List EP)) : List (List EP) :=
    match remaining with 
    | [] => 
      dbg_trace s!"Found all groups: {processedGroups.map (fun g => g.map (·.predicate))}"
      processedGroups
    | p::ps =>
      dbg_trace s!"Processing {p.predicate}"
      if processedGroups.any (·.contains p) then
        dbg_trace s!"  Already in a group, skipping"
        findAllGroups ps processedGroups
      else
        let pEvents := getEventVars p
        if pEvents.isEmpty then
          dbg_trace s!"  No events, creating singleton group"
          findAllGroups ps ([p] :: processedGroups)
        else
          dbg_trace s!"  Finding connected group starting with {p.predicate}"
          let connected := findConnected p []
          dbg_trace s!"  Found group: {connected.map (·.predicate)}"
          findAllGroups 
            (ps.filter (fun r => !connected.contains r))
            (connected :: processedGroups)

  findAllGroups preds []

def buildEventGroupFormula (group : List EP) (inner : Formula) (scopedEvents : List Var) : Formula :=
  let eventVars := group.foldl (fun acc ep => 
    let newVars := getEventVars ep |>.filter (fun v => !scopedEvents.contains v)
    dbg_trace s!"  Getting events from {ep.predicate}: {newVars} (already scoped: {scopedEvents})"
    (acc ++ newVars).eraseDups) []
  dbg_trace s!"buildEventGroupFormula for {group.map (·.predicate)}"
  dbg_trace s!"  All collected events: {eventVars}"
  dbg_trace s!"  Inner formula: {inner}"
  match eventVars with
  | [] => 
    dbg_trace "  No events - returning plain conjunction"
    Formula.conj (group.map Formula.atom ++ [inner])
  | _ => 
    dbg_trace s!"  Creating scope for events: {eventVars}"
    Formula.scope eventVars none 
      (Formula.conj (group.map Formula.atom ++ [inner]))

partial def buildEventConj (groups : List (List EP)) (inner : Formula) (scopedEvents : List Var := []) : Formula :=
  dbg_trace s!"buildEventConj processing {groups.length} groups:"
  dbg_trace s!"  Groups: {groups.map (fun g => g.map (·.predicate))}"
  dbg_trace s!"  Already scoped events: {scopedEvents}"
  match groups with
  | [] => 
    dbg_trace "  No groups - returning inner formula"
    inner
  | g :: gs => 
    dbg_trace s!"  Processing group {g.map (·.predicate)}"
    let result := buildEventConj gs inner scopedEvents
    -- Get all events from this group
    let groupEvents := g.foldl (fun acc ep =>
      (acc ++ getEventVars ep).eraseDups) []
    -- Only scope events not already scoped
    let newEvents := groupEvents.filter (fun v => !scopedEvents.contains v)
    if newEvents.isEmpty then
      dbg_trace "  No new events to scope - returning conjunction"
      Formula.conj (g.map Formula.atom ++ [result]) 
    else
      dbg_trace s!"  Creating scope for new events: {newEvents}"
      Formula.scope newEvents none
        (Formula.conj (g.map Formula.atom ++ [result]))

def containsEP (preds : List ScopedEP) (ep : EP) : Bool :=
  preds.any fun p => ep == p.predicate 

partial def analyzeFormula (f : Formula) : (List ScopeInfo × List ScopedEP) :=
  let rec analyze (f : Formula) (curScope : Option Var) (acc : List ScopeInfo × List ScopedEP) : (List ScopeInfo × List ScopedEP) :=
    match f with
    | Formula.atom ep => 
        let (scopes, preds) := acc
        if containsEP preds ep then
          (scopes, preds)
        else
          dbg_trace s!"Found atom {ep.predicate} in scope {curScope}"
          (scopes, { predicate := ep, scope := curScope } :: preds)
    | Formula.scope vars (some quant) inner =>
        let (scopes, preds) := acc
        dbg_trace s!"SCOPE ANALYSIS: Found scope {quant} with vars {vars}"
        let nextId := match curScope with
                     | none => 1
                     | some v => v.id + 1
        let newScope := Var.mk nextId 'h' #[]
        let normalized := if quant.startsWith "_" then quant.drop 1 else quant
        let scopeType := 
          if normalized == "every_q" then ScopeType.Universal 
          else if normalized == "the_q" || normalized == "def_explicit_q" then ScopeType.Definite
          else if normalized == "never_a_1" then 
            dbg_trace "SCOPE TYPE: Assigning NeverNeg type"
            ScopeType.NeverNeg
          else if normalized == "neg" then 
            dbg_trace "SCOPE TYPE: Assigning RegNeg type"
            ScopeType.RegNeg
          else if normalized == "colon_p_namely" then ScopeType.ColonNamely
          else 
            dbg_trace s!"SCOPE TYPE: Assigning Indefinite type to {quant}"
            ScopeType.Indefinite
        let newScopeInfo : ScopeInfo := {
          predicate := quant,
          boundVars := orderVarsForScoping vars.eraseDups,
          scopeType := scopeType,
          negVar := if vars.isEmpty then none else some vars.head!
        }
        dbg_trace s!"SCOPE CREATION: Created scope info: {newScopeInfo.predicate} type={toString newScopeInfo.scopeType} vars={newScopeInfo.boundVars} negVar={newScopeInfo.negVar}"
        analyze inner (some newScope) (newScopeInfo :: scopes, preds)
    | Formula.scope _ none inner =>
        analyze inner curScope acc
    | Formula.conj fs =>
        fs.foldl (fun acc f => analyze f curScope acc) acc

  analyze f none ([], [])

def canLiftToScope (ep : ScopedEP) (scope : ScopeInfo) (lowerScopes : List ScopeInfo) : Bool :=
  let deps := getNonEventVars ep.predicate
  let allVars := scope.boundVars ++ (lowerScopes.foldl (fun acc s => acc ++ s.boundVars) [])
  let result := deps.all (fun v => allVars.contains v)
  dbg_trace s!"Testing if {ep.predicate.predicate} can lift to scope with vars {allVars}"
  dbg_trace s!"  Non-event deps: {deps}"
  dbg_trace s!"  Result: {result}"
  result

partial def determineMinScope (ep : ScopedEP) (scopes : List ScopeInfo) : Option ScopeInfo :=
  let rec check : List ScopeInfo → List ScopeInfo → Option ScopeInfo
  | [], _ => none
  | s :: rest, lowerScopes =>
      if canLiftToScope ep s lowerScopes then some s
      else check rest (s :: lowerScopes)
  check scopes []

def buildScopedFormula (scope : ScopeInfo) (inner : Formula) : Formula :=
  dbg_trace s!"Building scoped formula for {scope.predicate} type {toString scope.scopeType} with negVar={scope.negVar}"
  Formula.scope scope.boundVars (some scope.predicate) inner

partial def buildFormula (scopes : List ScopeInfo) (preds : List ScopedEP) (scopedEvents : List Var) : Formula :=
  match scopes, preds with
  | [], [] => Formula.conj []
  | [], remaining => 
      dbg_trace s!"Building final event scopes for {remaining.map (·.predicate.predicate)}"
      buildEventConj (findEventGroups (remaining.map (·.predicate))) (Formula.conj []) scopedEvents
  | scope :: restScopes, preds =>
      dbg_trace s!"Processing scope {scope.predicate} (type: {toString scope.scopeType}) with vars {scope.boundVars}"
      let (hereEps, otherEps) := preds.partition (fun ep => 
        match determineMinScope ep (scope :: restScopes) with
        | some s => s == scope
        | none => false)
      dbg_trace s!"Predicates for this scope: {hereEps.map (·.predicate.predicate)}"
      dbg_trace s!"Remaining predicates: {otherEps.map (·.predicate.predicate)}"
      
      let groups := findEventGroups (hereEps.map (·.predicate))
      let groupEvents := groups.foldl (fun acc g => 
        (acc ++ (g.foldl (fun acc2 ep => acc2 ++ getEventVars ep) [])).eraseDups) []
      let newScopedEvents := scopedEvents ++ groupEvents
      let innerFormula := buildFormula restScopes otherEps newScopedEvents
      buildScopedFormula scope (buildEventConj groups innerFormula scopedEvents)

partial def minimizeScoping (f : Formula) : Formula :=
  dbg_trace s!"Starting minimizeScoping with formula: {f}"
  let (scopes, preds) := analyzeFormula f
  dbg_trace s!"Analysis found {scopes.length} scopes and {preds.length} predicates"
  dbg_trace s!"Scopes: {scopes.map (·.predicate)}"
  dbg_trace s!"Predicates: {preds.map (·.predicate.predicate)}"
  
  let result := buildFormula scopes preds []
  dbg_trace s!"minimizeScoping complete. Result:\n{result}"
  result

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (minimizeScoping)
