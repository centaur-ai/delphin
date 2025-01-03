import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Types
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

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

def isGuardedVar (v : Var) : Bool :=
  v.sort == 'r' || v.sort == 'b'

def isRstrVar (v : Var) : Bool := 
  v.sort == 'r'

def isBodyVar (v : Var) : Bool := 
  v.sort == 'b'

def getGuardType (v : Var) : Option Char :=
  if isRstrVar v then some 'r'
  else if isBodyVar v then some 'b'
  else none

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (
  getRequiredVarsForPredicate
  orderVarsForScoping
  getScopeVars
  getEventVars
  getNonEventVars
  getVarDeps
  isGuardedVar
  isRstrVar
  isBodyVar
  getGuardType
)
