import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS
open InsertionSort
open PWL.Transform
open Lean (HashMap)
open BEq

def getRequiredVarsForPredicate (ep : EP) : List Var :=
  let required := ep.rargs.map (fun x => x.2) |>.filter (fun v => v.sort == 'x' || v.sort == 'e' || v.sort == 'i')
  dbg_trace s!"Dependencies for {ep.predicate}: args={(ep.rargs.map (fun x => s!"{x.1}={x.2.sort}{x.2.id}"))} required={required}"
  required

def orderVarsForScoping (vars : List Var) : List Var :=
  insertionSort (vars.filter (fun v => v.sort == 'e'))
    ++ insertionSort (vars.filter (fun v => v.sort == 'i'))
    ++ insertionSort (vars.filter (fun v => v.sort == 'x'))

def getScopeVars (ep : EP) (level : Nat) : List Var :=
  let mainVars := ep.rargs.filter (fun p => 
    match p with 
    | (_, v) => v.sort == 'x' || v.sort == 'e' || v.sort == 'i')
    |>.map (fun p => match p with | (_, v) => v)
  
  let eventVars := ep.rargs.filter (fun p => 
    match p with | (_, v) => v.sort == 'e' || v.sort == 'i')
    |>.map (fun p => match p with | (_, v) => v)
  
  dbg_trace s!"ScopeVars for {ep.predicate}: mainVars={mainVars} eventVars={eventVars}"
  orderVarsForScoping ((mainVars ++ eventVars).eraseDups)

inductive ScopeType where 
  | Universal       : ScopeType  -- every_q
  | Definite       : ScopeType  -- the_q, def_explicit_q  
  | Indefinite     : ScopeType  -- proper_q, udef_q, etc
  | NeverNeg       : ScopeType  -- never_a_1 with its i variable
  | RegNeg         : ScopeType  -- neg with its e variable
  | ColonNamely    : ScopeType  -- colon_p_namely
  | RstrGuard      : ScopeType  -- protecting RSTR in the_q
  deriving Inhabited, BEq

instance : ToString ScopeType where
  toString := fun s => match s with
      | ScopeType.Universal => "Universal"
      | ScopeType.Definite => "Definite"
      | ScopeType.Indefinite => "Indefinite"
      | ScopeType.NeverNeg => "NeverNeg"
      | ScopeType.RegNeg => "RegNeg"
      | ScopeType.ColonNamely => "ColonNamely"
      | ScopeType.RstrGuard => "RstrGuard"

structure ScopeInfo where
  predicate : String
  boundVars : List Var
  scopeType : ScopeType
  negVar : Option Var := none
  deriving Inhabited

instance : ToString ScopeInfo where
  toString := fun si => s!"{si.predicate}({si.boundVars})"

structure FormulaState where
  declared : List Var := []
  neededVars : List Var := []
  formula : Formula := Formula.conj []
  movablePredicates : List EP := []
  deriving Inhabited

def canMoveUpScope (ep : EP) (availableVars : List Var) (level : Nat) : Bool :=
  let requiredVars := getRequiredVarsForPredicate ep
  let canMove := requiredVars.all (fun v => availableVars.contains v)
  dbg_trace s!"MoveUpScope {ep.predicate} level={level}: required={requiredVars} available={availableVars} canMove={canMove}"
  canMove

def checkPlacementLevel (ep : EP) (outerVars : List Var) (thisLevel : List Var) (level : Nat) : Bool :=
  let requiredVars := getRequiredVarsForPredicate ep
  let availInOuter := requiredVars.all (fun v => outerVars.contains v)
  let availHere := requiredVars.all (fun v => thisLevel.contains v)
  let someHere := requiredVars.any (fun v => thisLevel.contains v)
  dbg_trace s!"PlacementLevel {ep.predicate} level={level}: outer={outerVars} this={thisLevel} required={requiredVars} availUp={availInOuter} availHere={availHere} someHere={someHere}"
  someHere && !availInOuter || (availHere && !availInOuter)

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
  dbg_trace s!"EventVars for {ep.predicate}: {vars}"
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

instance : BEq ScopeInfo where
  beq si1 si2 := si1.predicate == si2.predicate && 
                 si1.boundVars == si1.boundVars && 
                 si1.scopeType == si2.scopeType &&
                 si1.negVar == si2.negVar

def canLiftToScope (ep : ScopedEP) (scope : ScopeInfo) (lowerScopes : List ScopeInfo) : Bool :=
  dbg_trace s!"LiftCheck {ep.predicate.predicate}: target={scope.predicate}[{scope.scopeType}] lower={lowerScopes.map (fun s => s!"{s.predicate}[{s.scopeType}]")}"
  (match ep.scope with 
  | some scopeVar => 
    if scopeVar.sort == 'r' then
      let canLift := scope.scopeType == ScopeType.RstrGuard
      dbg_trace s!"LiftCheck r-var {scopeVar}: toRstrGuard={canLift}"
      canLift
    else 
      if lowerScopes.any (fun s => 
        s.scopeType == ScopeType.RegNeg || 
        s.scopeType == ScopeType.NeverNeg || 
        s.scopeType == ScopeType.RstrGuard) then
        dbg_trace s!"LiftCheck: blocked by NEG/RstrGuard"
        false
      else
        let deps := getNonEventVars ep.predicate
        let allVars := scope.boundVars ++ (lowerScopes.foldl (fun acc s => acc ++ s.boundVars) [])
        let canLift := deps.all (fun v => allVars.contains v)
        dbg_trace s!"LiftCheck normal: deps={deps} available={allVars} canLift={canLift}"
        canLift
  | none =>
    if lowerScopes.any (fun s => 
      s.scopeType == ScopeType.RegNeg || 
      s.scopeType == ScopeType.NeverNeg || 
      s.scopeType == ScopeType.RstrGuard) then
      dbg_trace s!"LiftCheck unscoped: blocked by NEG/RstrGuard"
      false
    else
      let deps := getNonEventVars ep.predicate
      let allVars := scope.boundVars ++ (lowerScopes.foldl (fun acc s => acc ++ s.boundVars) [])
      let canLift := deps.all (fun v => allVars.contains v)
      dbg_trace s!"LiftCheck unscoped: deps={deps} available={allVars} canLift={canLift}"
      canLift)

def determineMinScope (ep : ScopedEP) (scopes : List ScopeInfo) : Option ScopeInfo :=
  dbg_trace s!"MinScope start: {ep.predicate.predicate} with scope={ep.scope}"
  dbg_trace s!"MinScope checking against scopes: {scopes.map (fun s => s!"{s.predicate}[{s.scopeType}]")}"
  
  let rec check (remaining : List ScopeInfo) (lowerScopes : List ScopeInfo) : Option ScopeInfo :=
    match remaining with 
    | [] => 
      dbg_trace s!"MinScope check: no remaining scopes"
      none
    | s :: rest => 
      dbg_trace s!"MinScope checking scope {s.predicate}[{s.scopeType}] for {ep.predicate.predicate}"
      dbg_trace s!"MinScope lower scopes: {lowerScopes.map (fun s => s!"{s.predicate}[{s.scopeType}]")}"
      if canLiftToScope ep s lowerScopes 
      then (
        dbg_trace s!"MinScope lift: found scope {s.predicate} for {ep.predicate.predicate}"
        some s
      ) else (
        dbg_trace s!"MinScope cannot lift {ep.predicate.predicate} to {s.predicate}, trying next scope"
        check rest (s :: lowerScopes))

  if (match ep.scope with | some scopeVar => scopeVar.sort == 'r' | none => false)
  then (
    if scopes.any (fun s => s.scopeType == ScopeType.Definite)
    then (
      dbg_trace s!"MinScope r-var: found Definite scope, deferring {ep.predicate.predicate}"
      none
    ) else (
      match scopes.find? (fun s => s.scopeType == ScopeType.RstrGuard) with
      | some scope => 
        dbg_trace s!"MinScope r-var: found RstrGuard {scope.predicate} for {ep.predicate.predicate}"
        some scope
      | none => 
        dbg_trace s!"MinScope r-var: no RstrGuard found for {ep.predicate.predicate}"
        none)
  ) else (
    dbg_trace s!"MinScope checking regular scopes for {ep.predicate.predicate}"
    check scopes [])

end PWL.Transform.MinScoping
