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

inductive ScopeType 
| Universal       -- every_q
| Definite       -- the_q, def_explicit_q  
| Indefinite     -- proper_q, udef_q, etc
| NeverNeg (i: Var)      -- never_a_1 with its i variable
| RegNeg (e: Var)        -- neg with its e variable
deriving Inhabited, BEq

instance : ToString ScopeType where
  toString 
  | ScopeType.Universal => "Universal"
  | ScopeType.Definite => "Definite"
  | ScopeType.Indefinite => "Indefinite"
  | ScopeType.NeverNeg i => s!"NeverNeg({i})"
  | ScopeType.RegNeg e => s!"RegNeg({e})"

structure ScopeInfo where
  predicate : String
  boundVars : List Var
  scopeType : ScopeType
  args : List (String × Var) := []
  deriving Inhabited

structure FormulaState where
  declared : List Var := []
  neededVars : List Var := []
  formula : Formula := Formula.conj []
  deriving Inhabited

instance : ToString ScopeInfo where
  toString si := s!"{si.predicate}({si.boundVars})"

instance : ToString (HashMap Var String) where
  toString m := s!"{m.toList}"

def getScopeType (pred : String) (args : List (String × Var)) : ScopeType :=
  let normalizedPred := fixName pred
  if normalizedPred == "every_q" then
    ScopeType.Universal
  else if normalizedPred == "the_q" || normalizedPred == "def_explicit_q" then
    ScopeType.Definite
  else
    ScopeType.Indefinite

/-- Extract predicates from a formula -/
partial def getPredicatesFromFormula : Formula → List EP
| Formula.atom ep => [ep]
| Formula.conj fs => 
  match fs with
  | [] => []
  | _ => fs.foldl (fun acc f => acc ++ getPredicatesFromFormula f) []
| Formula.scope _ _ inner => getPredicatesFromFormula inner
| Formula.neg _ inner => getPredicatesFromFormula inner

/-- Extract scope info from formula scope -/
partial def getFormulaScopes : Formula → List ScopeInfo  
| Formula.atom _ => []
| Formula.conj fs => 
  match fs with
  | [] => []
  | _ => fs.foldl (fun acc f => acc ++ getFormulaScopes f) []
| Formula.scope vars (some pred) inner => 
  let scopeType := getScopeType pred []
  let innerScopes := getFormulaScopes inner
  { predicate := pred,
    boundVars := vars.eraseDups,
    scopeType := scopeType } :: innerScopes
| Formula.scope _ none inner => getFormulaScopes inner
| Formula.neg negType inner => 
  let scopeType := match negType with
    | NegationType.Never i => ScopeType.NeverNeg i
    | NegationType.NegWithEvent e => ScopeType.RegNeg e
  let innerScopes := getFormulaScopes inner
  { predicate := match negType with
      | NegationType.Never i => "never_a_1"
      | NegationType.NegWithEvent e => "neg",
    boundVars := [],  -- Negations don't bind variables but maintain scope
    scopeType := scopeType } :: innerScopes

/-- Extract x-variables used in predicate -/
def getXVars (ep : EP) : List Var :=
  dbg_trace s!"Extracting x-variables from EP: {ep}"
  (ep.rargs.filter (·.2.sort == 'x')
   |>.map (·.2)
   |>.eraseDups)

/-- Create scoped formula while preserving negation scoping -/
def createScopedFormula (formula : Formula) (univVars defVars indefVars : List Var) 
    (negInfo : List ScopeInfo) (quantMap : HashMap Var String) : Formula :=
  dbg_trace s!"Creating scoped formula with univVars={univVars} defVars={defVars} indefVars={indefVars}"
  
  let withUniv := match univVars with
    | [] => formula
    | vars =>
      dbg_trace s!"Adding universal scope for vars: {vars}"
      Formula.scope vars (some "every_q") formula

  -- Handle negation scoping here - maintain original scope position with variables
  let withNeg := match negInfo with
    | [] => withUniv
    | negScopes => 
      negScopes.foldl (fun acc scope =>
        match scope.scopeType with
        | ScopeType.NeverNeg i => 
          Formula.neg (NegationType.Never i) acc
        | ScopeType.RegNeg e =>
          Formula.neg (NegationType.NegWithEvent e) acc
        | _ => acc) withUniv

  let withDef := defVars.foldl (fun acc v =>
    match quantMap.find? v with
    | some quant => 
      dbg_trace s!"Adding definite scope for var {v} with quantifier {quant}"
      Formula.scope [v] (some quant) acc
    | none => acc) withNeg

  match indefVars with
  | [] => withDef
  | _ => 
    match indefVars.head? with
    | some v =>
      let quant := quantMap.find? v
      dbg_trace s!"Adding indefinite scope for vars {indefVars} with quantifier {quant}"
      Formula.scope indefVars quant withDef
    | none => withDef

/-- Build formula from predicates and scopes -/
def buildFormula (preds : List EP) (scopes : List ScopeInfo) : Formula :=
  dbg_trace s!"Building formula with {preds.length} predicates and {scopes.length} scopes"
  
  let initState : FormulaState := {
    declared := [],
    neededVars := [],
    formula := Formula.conj []
  }
  
  let baseState := preds.foldl (fun (state : FormulaState) (ep : EP) =>
    dbg_trace s!"Processing predicate: {ep}"
    let varsUsed := getXVars ep
    let newNeeded := varsUsed.filter (fun v => !state.declared.contains v)
    { state with
      neededVars := (state.neededVars ++ newNeeded).eraseDups,
      formula := Formula.conj (Formula.atom ep :: match state.formula with
        | Formula.conj fs => fs
        | f => [f]) }) initState

  let univVars := baseState.neededVars.filter (fun v =>
    scopes.any (fun si => 
      match si.scopeType with
      | ScopeType.Universal => si.boundVars.contains v
      | _ => false))
  
  let defVars := baseState.neededVars.filter (fun v =>
    scopes.any (fun si =>
      match si.scopeType with
      | ScopeType.Definite => si.boundVars.contains v
      | _ => false))

  let indefVars := baseState.neededVars.filter (fun v =>
    scopes.any (fun si =>
      match si.scopeType with
      | ScopeType.Indefinite => si.boundVars.contains v
      | _ => false))

  let negScopes := scopes.filter (fun si =>
    match si.scopeType with
    | ScopeType.NeverNeg _ => true
    | ScopeType.RegNeg _ => true
    | _ => false)

  let quantMap := scopes.foldl (fun map si =>
    match si.boundVars.head? with
    | some v => map.insert v si.predicate
    | none => map) HashMap.empty

  dbg_trace s!"Final categorization - Universal:{univVars} Definite:{defVars} Indefinite:{indefVars} Negation:{negScopes}"
  
  createScopedFormula baseState.formula univVars defVars indefVars negScopes quantMap

def minimizeScoping (f : Formula) : Formula :=
  dbg_trace "Starting minimizeScoping"
  let preds := getPredicatesFromFormula f
  let scopes := getFormulaScopes f 
  buildFormula preds scopes

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (minimizeScoping)
