import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Mrs.PwlTransformMinScoping_Analysis
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS
open InsertionSort
open PWL.Transform
open Lean (HashMap)
open BEq

def canMoveUpScope (ep : EP) (availableVars : List Var) (level : Nat) : Bool :=
  let requiredVars := getRequiredVarsForPredicate ep
  let canMove := requiredVars.all (fun v => availableVars.contains v)
  dbg_trace s!"=== PREDICATE {ep.predicate} at level {level} ==="
  dbg_trace s!"  Label: h{ep.label.id}"
  dbg_trace s!"  Dependencies: {requiredVars.map (fun v => s!"{v.sort}{v.id}")}"
  dbg_trace s!"  Available: {availableVars.map (fun v => s!"{v.sort}{v.id}")}"
  dbg_trace s!"  Decision: {if canMove then "CAN MOVE UP" else "MUST STAY"}"
  canMove

def checkPlacementLevel (ep : EP) (outerVars : List Var) (thisLevel : List Var) (level : Nat) : Bool :=
  let requiredVars := getRequiredVarsForPredicate ep
  let outerAvailable := requiredVars.all (fun v => outerVars.contains v)
  let thisAvailable := requiredVars.all (fun v => thisLevel.contains v)
  let stayHere := thisAvailable && !outerAvailable
  dbg_trace s!"  Final placement for {ep.predicate}:"
  dbg_trace s!"    Required: {requiredVars.map (fun v => s!"{v.sort}{v.id}")}"
  dbg_trace s!"    Available in outer: {outerVars.map (fun v => s!"{v.sort}{v.id}")}"
  dbg_trace s!"    Available here: {thisLevel.map (fun v => s!"{v.sort}{v.id}")}"
  dbg_trace s!"    Decision: {if stayHere then "STAY AT THIS LEVEL" else "TRY HIGHER"}"
  stayHere

mutual 
  partial def minimizeScopeRegion (f : Formula) (level : Nat := 0) : Formula :=
    dbg_trace s!"=== SCOPE REGION LEVEL {level} ==="
    match f with
    | Formula.atom ep => 
      dbg_trace s!"  Processing atomic predicate {ep.predicate}(h{ep.label.id})"
      f
    | Formula.conj fs => 
      dbg_trace s!"  Processing conjunction with {fs.length} parts"
      let preds := getPredicatesFromFormula f level
      buildMinimalFormula preds f [] level
    | Formula.scope vars quant inner =>
      dbg_trace s!"  Processing scope with vars: {vars.map (fun v => s!"{v.sort}{v.id}")}"
      dbg_trace s!"  Quantifier: {quant}"
      Formula.scope vars quant (minimizeScopeRegion inner (level + 1))

  partial def buildMinimalFormula (preds : List EP) (f : Formula) 
    (outerVars : List Var) (level : Nat) : Formula :=
    match f with
    | Formula.atom _ => f
    | Formula.scope vars quant inner => 
      dbg_trace s!"=== BUILD SCOPE LEVEL {level} ==="
      dbg_trace s!"  Outer vars: {outerVars.map (fun v => s!"{v.sort}{v.id}")}"
      dbg_trace s!"  This scope vars: {vars.map (fun v => s!"{v.sort}{v.id}")}"
      
      match quant with
      | some q =>
        let normalized := if q.startsWith "_" then q.drop 1 else q
        if ["never_a_1", "neg", "colon_p_namely"].contains normalized then
          dbg_trace s!"  Found fixed scope: {normalized}"
          Formula.scope vars (some normalized) 
            (buildMinimalFormula preds inner (outerVars ++ vars) (level + 1))
        else 
          dbg_trace s!"  Processing quantifier: {normalized}"
          let innerResult := buildMinimalFormula preds inner 
            (outerVars ++ vars) (level + 1)
          Formula.scope vars quant innerResult
      | none =>
        let innerResult := buildMinimalFormula preds inner 
          (outerVars ++ vars) (level + 1)
        Formula.scope vars none innerResult
    | _ =>
      dbg_trace s!"=== BUILDING MINIMAL STATE AT LEVEL {level} ==="
      let startState : FormulaState := { declared := [], neededVars := [], formula := Formula.conj [] }
      
      let baseState := preds.foldl (fun (state : FormulaState) (ep : EP) =>
        let varsUsed := getScopeVars ep level
        let upwardMovable := canMoveUpScope ep outerVars level
        let shouldStayHere := checkPlacementLevel ep outerVars varsUsed level
        let newNeeded := varsUsed.filter (fun v => !state.declared.contains v)
        
        dbg_trace s!"  Analyzing {ep.predicate}(h{ep.label.id}):"
        dbg_trace s!"    Used vars: {varsUsed.map (fun v => s!"{v.sort}{v.id}")}"
        dbg_trace s!"    New needed: {newNeeded.map (fun v => s!"{v.sort}{v.id}")}"
        dbg_trace s!"    Placement: {if shouldStayHere then "KEEP HERE" else "COULD MOVE UP"}"
        
        { state with
          neededVars := (state.neededVars ++ newNeeded).eraseDups,
          formula := Formula.conj (Formula.atom ep :: 
            match state.formula with
            | Formula.conj fs => fs
            | f => [f]) }) startState

      dbg_trace s!"=== SCOPE ANALYSIS AT LEVEL {level} ==="
      
      let scopes := getFormulaScopes f level
      let negScopes := scopes.filter fun si =>
        match si.scopeType with 
        | ScopeType.NeverNeg | ScopeType.RegNeg | ScopeType.ColonNamely => true
        | _ => false
      
      dbg_trace s!"  Fixed scopes found: {negScopes.map (fun s => s.predicate)}"
      
      let allVars := baseState.neededVars
      let entityVars := allVars.filter (fun v => v.sort == 'x')
      let eventVars := allVars.filter (fun v => v.sort == 'e')

      let univVars := entityVars.filter (fun v =>
        scopes.any fun si => 
          match si.scopeType with
          | ScopeType.Universal => si.boundVars.contains v
          | _ => false)
      
      let defVars := entityVars.filter (fun v =>
        scopes.any fun si =>
          match si.scopeType with
          | ScopeType.Definite => si.boundVars.contains v
          | _ => false)
      
      let indefVars := entityVars.filter (fun v =>
        scopes.any fun si =>
          match si.scopeType with
          | ScopeType.Indefinite => si.boundVars.contains v
          | _ => false)
      
      dbg_trace s!"=== VARIABLE CLASSIFICATION AT LEVEL {level} ==="
      dbg_trace s!"  Event variables: {eventVars.map (fun v => s!"{v.sort}{v.id}")}"
      dbg_trace s!"  Universal vars: {univVars.map (fun v => s!"{v.sort}{v.id}")}"
      dbg_trace s!"  Definite vars: {defVars.map (fun v => s!"{v.sort}{v.id}")}"
      dbg_trace s!"  Indefinite vars: {indefVars.map (fun v => s!"{v.sort}{v.id}")}"

      -- Build scoped formula from inside out
      dbg_trace "=== CONSTRUCTING SCOPES ==="
      let withEvents := 
        if eventVars.isEmpty then
          dbg_trace "  No event variables to scope"
          baseState.formula
        else
          dbg_trace s!"  Adding event scope for: {eventVars.map (fun v => s!"{v.sort}{v.id}")}"
          Formula.scope (orderVarsForScoping eventVars) none baseState.formula

      let withUniv := univVars.foldl (fun acc v => 
        dbg_trace s!"  Adding universal scope for: {v.sort}{v.id}"
        Formula.scope [v] (some "every_q") acc) withEvents
      
      let withDef := defVars.foldl (fun acc v => 
        dbg_trace s!"  Adding definite scope for: {v.sort}{v.id}"
        Formula.scope [v] (some "the_q") acc) withUniv

      let quantMap := scopes.foldl (fun map si =>
        si.boundVars.foldl (fun m v => 
          match m.find? v with
          | none => m.insert v si.predicate
          | some _ => m) map) HashMap.empty

      let withIndef := indefVars.foldl (fun acc v =>
        match quantMap.find? v with
        | some quant => 
          dbg_trace s!"  Adding {quant} scope for: {v.sort}{v.id}"
          Formula.scope [v] (some quant) acc
        | none => 
          dbg_trace s!"  No quantifier found for: {v.sort}{v.id}"
          acc) withDef

      let withNeg := negScopes.foldl (fun acc scope =>
        match scope.negVar with
        | some var => 
          dbg_trace s!"  Adding {scope.predicate} scope for: {var.sort}{var.id}"
          Formula.scope [var] (some scope.predicate) acc
        | none => 
          dbg_trace s!"  Unable to add scope for: {scope.predicate} - no variable"
          acc) withIndef
      
      dbg_trace s!"=== SCOPE CONSTRUCTION COMPLETE FOR LEVEL {level} ==="
      dbg_trace s!"  Event scopes: {eventVars.length}"
      dbg_trace s!"  Quantifier scopes: {univVars.length + defVars.length + indefVars.length}"
      dbg_trace s!"  Fixed scopes: {negScopes.length}"
      withNeg
end

def minimizeScoping (f : Formula) : Formula :=
  dbg_trace "=== STARTING MINIMIZATION ==="
  let result := minimizeScopeRegion f
  dbg_trace "=== MINIMIZATION COMPLETE ==="
  result

end PWL.Transform.MinScoping
