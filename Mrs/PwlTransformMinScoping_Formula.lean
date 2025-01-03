import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Mrs.PwlTransformMinScoping_Analysis
import Mrs.PwlTransformMinScoping_Events 
import Mrs.PwlTransformMinScoping_Scopes
import Mrs.PwlTransformSerializeTheQ
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

def buildScopedFormula (scope : ScopeInfo) (inner : Formula) : Formula :=
  dbg_trace s!"MINSCOPE.buildScopedFormula: scope={scope.predicate} vars={scope.boundVars}"
  match scope.scopeType with
  | ScopeType.RstrGuard => Formula.scope [] (some "rstr_guard") inner
  | _ => Formula.scope scope.boundVars (some scope.predicate) inner

partial def getVarDependencies (preds : List ScopedEP) (v : Var) : List Var :=
  -- Get direct dependencies - where var appears with other x vars in same pred
  let directDeps := preds.foldl (fun acc p =>
    if p.predicate.rargs.any (fun a => a.2 == v) then
      let deps := p.predicate.rargs.foldl (fun acc2 a =>
        if a.2.sort == 'x' && a.2 != v then
          a.2 :: acc2
        else acc2) []
      dbg_trace s!"MINSCOPE.deps: var {v} direct deps from {p.predicate.predicate}: {deps}"
      acc ++ deps
    else acc) []
  
  -- Get event-mediated dependencies - where vars connect through event vars
  let eventDeps := preds.foldl (fun acc p =>
    if p.predicate.rargs.any (fun a => a.2 == v) then
      let eventVars := p.predicate.rargs.filter (fun a => a.2.sort == 'e') |>.map (·.2)
      dbg_trace s!"MINSCOPE.deps: var {v} in {p.predicate.predicate} has events {eventVars}"
      let connectedPreds := preds.filter (fun p2 => 
        eventVars.any (fun ev => p2.predicate.rargs.any (fun a => a.2 == ev)))
      let connectedVars := connectedPreds.foldl (fun acc2 p2 =>
        let newVars := p2.predicate.rargs.filter (fun a => a.2.sort == 'x' && a.2 != v) |>.map (·.2)
        dbg_trace s!"MINSCOPE.deps: connected pred {p2.predicate.predicate} adds vars {newVars}"
        acc2 ++ newVars) []
      acc ++ connectedVars
    else acc) []

  let allDeps := (directDeps ++ eventDeps).eraseDups
  dbg_trace s!"MINSCOPE.deps: var {v} total deps: {allDeps}"
  allDeps

partial def buildDependencyGraph (scopes : List ScopeInfo) (preds : List ScopedEP) 
    : List (ScopeInfo × List ScopeInfo) :=
  dbg_trace s!"MINSCOPE.graph: building for {scopes.length} scopes"
  scopes.map (fun s => 
    match s.boundVars.head? with
    | none => (s, [])
    | some v => 
      let depVars := getVarDependencies preds v
      let depScopes := scopes.filter (fun s2 => 
        s2 != s && s2.boundVars.any (fun v2 => depVars.contains v2))
      dbg_trace s!"MINSCOPE.graph: scope {s.predicate} for {v} depends on: {depScopes.map (fun s => s.boundVars)}"
      (s, depScopes))

def findRoots (graph : List (ScopeInfo × List ScopeInfo)) : List ScopeInfo :=
  let allDeps := graph.foldl (fun acc (_,deps) => acc ++ deps) []
  let roots := graph.filter (fun (s,_) => !(allDeps.any (fun d => d == s))) |>.map (·.1)
  dbg_trace s!"MINSCOPE.sort: roots found: {roots.map (fun r => r.boundVars)}"
  roots

partial def topoSort (graph : List (ScopeInfo × List ScopeInfo)) : List ScopeInfo :=
  let rec topoSortWithVisited (graph : List (ScopeInfo × List ScopeInfo)) 
                             (visited : List ScopeInfo) : List ScopeInfo :=
    if graph.isEmpty then []
    else
      let roots := graph.filter (fun (s,deps) => 
        deps.all (fun d => visited.contains d)) |>.map (·.1)
      match roots with 
      | [] => 
          -- If no roots and graph not empty, we have a cycle - just pick first node
          let first := graph.head!.1
          let remainingGraph := graph.filter (fun (s,_) => s != first)
          dbg_trace s!"MINSCOPE.sort: cycle detected, choosing {first.boundVars}"
          first :: topoSortWithVisited remainingGraph (first :: visited)
      | _ =>
          dbg_trace s!"MINSCOPE.sort: using roots {roots.map (fun r => r.boundVars)}"
          let remainingGraph := graph.filter (fun (s,_) => !roots.contains s)
          roots ++ topoSortWithVisited remainingGraph (visited ++ roots)

  topoSortWithVisited graph []

def sortScopes (scopes : List ScopeInfo) (preds : List ScopedEP) : List ScopeInfo :=
  -- Split proper_q and other scopes
  let (properScopes, otherScopes) := scopes.partition (fun s => 
    s.predicate == "proper_q" || s.predicate == "_proper_q")
  dbg_trace s!"MINSCOPE.sort: found {properScopes.length} proper_q, {otherScopes.length} other scopes"

  -- Sort each group by dependencies independently
  let properGraph := buildDependencyGraph properScopes preds
  let otherGraph := buildDependencyGraph otherScopes preds

  let properSorted := topoSort properGraph
  let otherSorted := topoSort otherGraph

  dbg_trace s!"MINSCOPE.sort: proper_q order: {properSorted.map (fun s => s.boundVars)}"
  dbg_trace s!"MINSCOPE.sort: other order: {otherSorted.map (fun s => s.boundVars)}"
  
  properSorted ++ otherSorted

mutual

partial def buildEventConj (groups : List (List EP)) (inner : Formula) (scopedEvents : List Var) : Formula :=
  match groups with
  | [] => inner
  | g :: gs => 
    let groupEvents := g.foldl (fun acc ep => (acc ++ getEventVars ep).eraseDups) []
    let newEvents := groupEvents.filter (fun v => !(scopedEvents.any (fun e => e == v)))
    if newEvents.isEmpty then
      Formula.conj (g.map Formula.atom ++ [buildEventConj gs inner scopedEvents])
    else  
      Formula.scope newEvents none
        (Formula.conj (g.map Formula.atom ++ [buildEventConj gs inner (scopedEvents ++ newEvents)]))

partial def buildScopedFormulas (scopes : List ScopeInfo) (preds : List ScopedEP) 
    (events : List Var) (depth : Nat) : Formula :=
  match depth with
  | 0 => Formula.conj []  -- Emergency recursion limit
  | depth + 1 =>
    match scopes with
    | [] => buildFormula [] preds events
    | scope :: restScopes =>
      match scope.scopeType with
      | ScopeType.Definite =>
        match scope.boundVars.head? with
        | none => unreachable!
        | some boundVar =>
          let rstrVar := {id := boundVar.id, sort := 'r', props := #[]}
          let bodyVar := {id := boundVar.id, sort := 'b', props := #[]}
          
          let (rstrPreds, bodyPreds) := preds.partition (fun ep =>
            match ep.scope with
            | none => false
            | some scopeVar => isRstrVar scopeVar && scopeVar.id == boundVar.id)
          dbg_trace s!"MINSCOPE.formula: definite scope partitioned {rstrPreds.length}/{bodyPreds.length}"

          let rstrFormula := buildScopedFormulas restScopes rstrPreds events depth
          let bodyFormula := buildScopedFormulas restScopes bodyPreds events depth
          
          let guardedRstr := Formula.scope [rstrVar] (some "rstr_guard") rstrFormula
          let guardedBody := Formula.scope [bodyVar] (some "body_guard") bodyFormula
          
          buildScopedFormula scope (Formula.conj [guardedRstr, guardedBody])

      | _ =>
        -- Partition predicates for this scope
        let (scopePreds, otherPreds) := preds.partition (fun ep =>
          match ep.scope with
          | none => false
          | some scopeVar => scope.boundVars.any (fun v => v == scopeVar))
        dbg_trace s!"MINSCOPE.formula: scope {scope.predicate} partitioned {scopePreds.length}/{otherPreds.length}"

        -- Handle predicates at this scope level
        let predsFormula := Formula.conj (scopePreds.map (·.predicate) |>.map Formula.atom)
        
        -- Recursively handle remaining scopes
        let innerFormula := buildScopedFormulas restScopes otherPreds events depth
        
        buildScopedFormula scope (Formula.conj [predsFormula, innerFormula])

partial def buildFormula (scopes : List ScopeInfo) (preds : List ScopedEP) 
    (scopedEvents : List Var) : Formula :=
  match scopes with
  | [] => 
    match preds with
    | [] => Formula.conj []
    | remaining => 
      -- Just handle event groups for remaining preds
      let groups := findEventGroups (remaining.map (·.predicate))
      dbg_trace s!"MINSCOPE.formula: handling {groups.length} event groups"
      buildEventConj groups (Formula.conj []) scopedEvents
  | _ =>
    -- Sort scopes based on dependencies
    let sortedScopes := sortScopes scopes preds
    dbg_trace s!"MINSCOPE.formula: sorted scope order: {sortedScopes.map (fun s => (s.predicate, s.boundVars))}"

    -- Build formula with recursion depth limit
    buildScopedFormulas sortedScopes preds scopedEvents 1000

end

def minimizeScoping (f : Formula) : Formula := 
  dbg_trace s!"MINSCOPE.minimizeScoping: input formula={f}"
  let (scopes, preds) := analyzeFormula f
  buildFormula scopes preds []

end PWL.Transform.MinScoping
