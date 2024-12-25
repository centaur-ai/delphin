import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS
open InsertionSort
open PWL.Transform
open Lean (HashMap)
open BEq

def getRequiredVarsForPredicate (ep : EP) : List Var :=
  let required := ep.rargs.map (fun x => x.2) |>.filter (fun v => v.sort == 'x' || v.sort == 'e' || v.sort == 'i')
  dbg_trace s!"### Analyzing dependencies for predicate: {ep.predicate}"
  dbg_trace s!"  Arguments: {ep.rargs.map (fun x => s!"{x.1}={x.2.sort}{x.2.id}")}"
  dbg_trace s!"  Required variables: {required.map (fun v => s!"{v.sort}{v.id}")}"
  dbg_trace s!"  Dependency count: {required.length}"
  required

def orderVarsForScoping (vars : List Var) : List Var :=
  insertionSort (vars.filter (fun v => v.sort == 'e'))
    ++ insertionSort (vars.filter (fun v => v.sort == 'i'))
    ++ insertionSort (vars.filter (fun v => v.sort == 'x'))

def getScopeVars (ep : EP) (level : Nat) : List Var :=
  let indent := String.mk (List.replicate (level * 2) ' ')
  dbg_trace s!"{indent}### Analyzing variables for predicate: {ep.predicate}"
  
  -- Get main variables (x, e, and i sorts)
  let mainVars := ep.rargs.filter (fun p => 
    match p with 
    | (_, v) => v.sort == 'x' || v.sort == 'e' || v.sort == 'i')
    |>.map (fun p => match p with | (_, v) => v)
  
  dbg_trace s!"{indent}Main variables: {toString mainVars}"
  
  -- Get event variables separately
  let eventVars := ep.rargs.filter (fun p => 
    match p with | (_, v) => v.sort == 'e' || v.sort == 'i')
    |>.map (fun p => match p with | (_, v) => v)
  
  dbg_trace s!"{indent}Event variables: {toString eventVars}"
  
  -- Combine and order variables
  let result := orderVarsForScoping ((mainVars ++ eventVars).eraseDups)
  dbg_trace s!"{indent}Final ordered variables: {toString result}"
  result

inductive ScopeType where 
  | Universal       : ScopeType  -- every_q
  | Definite       : ScopeType  -- the_q, def_explicit_q  
  | Indefinite     : ScopeType  -- proper_q, udef_q, etc
  | NeverNeg       : ScopeType  -- never_a_1 with its i variable
  | RegNeg         : ScopeType  -- neg with its e variable
  | ColonNamely    : ScopeType  -- colon_p_namely
  deriving Inhabited, BEq

instance : ToString ScopeType where
  toString := fun s => match s with
      | ScopeType.Universal => "Universal"
      | ScopeType.Definite => "Definite"
      | ScopeType.Indefinite => "Indefinite"
      | ScopeType.NeverNeg => "NeverNeg"
      | ScopeType.RegNeg => "RegNeg"
      | ScopeType.ColonNamely => "ColonNamely"

structure ScopeInfo where
  predicate : String
  boundVars : List Var
  scopeType : ScopeType
  negVar : Option Var := none
  deriving Inhabited

instance : ToString ScopeInfo where
  toString := fun si => s!"{si.predicate}({si.boundVars})"

structure ScopingResult where
  formula : Formula
  liftedPreds : List EP := []
  deriving Inhabited

structure FormulaState where
  declared : List Var := []
  neededVars : List Var := []
  formula : Formula := Formula.conj []
  movablePredicates : List EP := []
  deriving Inhabited

def canMoveUpScope (ep : EP) (availableVars : List Var) (level : Nat) : Bool :=
  dbg_trace s!"scopeVars {level} moveup {ep.predicate} avail={availableVars}"
  let requiredVars := getRequiredVarsForPredicate ep
  let dependencyCount := requiredVars.length
  let canMove := requiredVars.all (fun v => availableVars.contains v)
  canMove

def checkPlacementLevel (ep : EP) (outerVars : List Var) (thisLevel : List Var) (level : Nat) : Bool :=
  let requiredVars := getRequiredVarsForPredicate ep
  let availInOuter := requiredVars.all (fun v => outerVars.contains v)
  let availHere := requiredVars.all (fun v => thisLevel.contains v)
  let someHere := requiredVars.any (fun v => thisLevel.contains v)
  dbg_trace s!"scopeVars {level} placement {ep.predicate} outer={outerVars} this={thisLevel} req={requiredVars} availUp={availInOuter} availHere={availHere} someHere={someHere}"
  someHere && !availInOuter || (availHere && !availInOuter)

end PWL.Transform.MinScoping
