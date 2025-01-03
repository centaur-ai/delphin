import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

/-- Information about arguments parsed from predicates -/
structure ArgInfo where
  firstArg : Option (String × Var)
  otherArgs : List (String × Var)
  deriving Inhabited

/-- Type of scope used for quantifiers and guards -/
inductive ScopeType where 
  | Universal       : ScopeType  -- every_q
  | Definite       : ScopeType  -- the_q, def_explicit_q  
  | Indefinite     : ScopeType  -- proper_q, udef_q, etc
  | NeverNeg       : ScopeType  -- never_a_1 with its i variable
  | RegNeg         : ScopeType  -- neg with its e variable
  | ColonNamely    : ScopeType  -- colon_p_namely
  | RstrGuard      : ScopeType  -- protecting RSTR in the_q
  | BodyGuard      : ScopeType  -- protecting BODY in the_q
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
      | ScopeType.BodyGuard => "BodyGuard"

/-- Information about a scope and its variables -/
structure ScopeInfo where
  predicate : String
  boundVars : List Var
  scopeType : ScopeType
  negVar : Option Var := none
  deriving Inhabited

instance : ToString ScopeInfo where
  toString := fun si => s!"{si.predicate}({si.boundVars})"

instance : BEq ScopeInfo where
  beq si1 si2 := si1.predicate == si2.predicate && 
                 si1.boundVars == si1.boundVars && 
                 si1.scopeType == si2.scopeType &&
                 si1.negVar == si2.negVar

/-- State tracked during formula construction -/
structure FormulaState where
  declared : List Var := []
  neededVars : List Var := []
  formula : Formula := Formula.conj []
  movablePredicates : List EP := []
  deriving Inhabited

/-- EP with scope information -/
structure ScopedEP where
  predicate : EP
  scope : Option Var
  deriving Inhabited, BEq

end PWL.Transform.MinScoping
