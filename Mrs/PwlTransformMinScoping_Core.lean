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

structure FormulaState where
  declared : List Var := []
  neededVars : List Var := []
  formula : Formula := Formula.conj []
  deriving Inhabited

def orderVarsForScoping (vars : List Var) : List Var :=
  insertionSort (vars.filter (fun v => v.sort == 'e'))
    ++ insertionSort (vars.filter (fun v => v.sort == 'x'))

def getScopeVars (ep : EP) (level : Nat) : List Var :=
  let indent := String.mk (List.replicate (level * 2) ' ')
  dbg_trace s!"{indent}### Analyzing variables for predicate: {ep.predicate}"
  
  -- Get main variables (x and e sorts)
  let mainVars := ep.rargs.filter (fun p => 
    match p with 
    | (_, v) => v.sort == 'x' || v.sort == 'e')
    |>.map (fun p => match p with | (_, v) => v)
  
  dbg_trace s!"{indent}Main variables: {toString mainVars}"
  
  -- Get event variables separately
  let eventVars := ep.rargs.filter (fun p => 
    match p with | (_, v) => v.sort == 'e')
    |>.map (fun p => match p with | (_, v) => v)
  
  dbg_trace s!"{indent}Event variables: {toString eventVars}"
  
  -- Combine and order variables
  let result := orderVarsForScoping ((mainVars ++ eventVars).eraseDups)
  dbg_trace s!"{indent}Final ordered variables: {toString result}"
  result

end PWL.Transform.MinScoping
