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
| NeverNeg       -- never_a_1 with its i variable
| RegNeg         -- neg with its e variable
deriving Inhabited, BEq

instance : ToString ScopeType where
  toString 
  | ScopeType.Universal => "Universal"
  | ScopeType.Definite => "Definite"
  | ScopeType.Indefinite => "Indefinite"
  | ScopeType.NeverNeg => "NeverNeg"
  | ScopeType.RegNeg => "RegNeg"

structure ScopeInfo where
  predicate : String
  boundVars : List Var
  scopeType : ScopeType
  negVar : Option Var := none  -- For storing e/i vars from negation
deriving Inhabited

instance : ToString ScopeInfo where
  toString si := s!"{si.predicate}({si.boundVars})"

structure FormulaState where
  declared : List Var := []
  neededVars : List Var := []
  formula : Formula := Formula.conj []
deriving Inhabited

partial def getPredicatesFromFormula : Formula → List EP
| Formula.atom ep => [ep]
| Formula.conj fs => 
  match fs with 
  | [] => []
  | _ => fs.foldl (fun acc f => acc ++ getPredicatesFromFormula f) []
| Formula.scope _ _ inner => getPredicatesFromFormula inner

def getXVars (ep : EP) : List Var :=
  dbg_trace s!"Extracting x-variables from EP: {ep}"
  (ep.rargs.filter (·.2.sort == 'x')
   |>.map (·.2)
   |>.eraseDups)

partial def getFormulaScopes : Formula → List ScopeInfo
| Formula.atom _ => []  
| Formula.conj fs => 
  match fs with
  | [] => []
  | _ => 
    dbg_trace "getFormulaScopes processing conjunction"
    fs.foldl (fun acc f => acc ++ getFormulaScopes f) []
| Formula.scope vars (some pred) inner => 
  dbg_trace s!"getFormulaScopes examining scope with predicate: {pred}"
  let normalized := if pred.startsWith "_" then pred.drop 1 else pred
  let scopeType := 
    if normalized == "every_q" then
      ScopeType.Universal 
    else if normalized == "the_q" || normalized == "def_explicit_q" then
      ScopeType.Definite
    else if normalized == "never_a_1" then
      dbg_trace s!"Found never_a_1 negation scope with vars: {vars}"
      ScopeType.NeverNeg
    else if normalized == "neg" then
      dbg_trace s!"Found neg scope with vars: {vars}"
      ScopeType.RegNeg
    else
      ScopeType.Indefinite
  let info : ScopeInfo := {
    predicate := normalized,
    boundVars := vars.eraseDups,
    scopeType := scopeType,
    negVar := if vars.isEmpty then none else some vars.head!
  }
  dbg_trace s!"Created scope info: {info}"
  info :: getFormulaScopes inner
| Formula.scope _ none inner => getFormulaScopes inner

mutual
  partial def combineScopes (vars : List Var) (quant : String) (inner : Formula) : Formula :=
    dbg_trace s!"Combining scopes for {quant} with vars {vars}"
    match vars with
    | [] => inner
    | _ => Formula.scope vars (some quant) inner

  partial def minimizeScopeRegion (f : Formula) : Formula :=
    dbg_trace s!"minimizeScopeRegion examining: {f}"
    match f with
    | Formula.atom _ => f
    | Formula.conj fs => 
        let preds := getPredicatesFromFormula f
        buildMinimalFormula preds f
    | Formula.scope vars quant inner =>
        Formula.scope vars quant (minimizeScopeRegion inner)

  partial def buildMinimalFormula (preds : List EP) (f : Formula) : Formula := 
    match f with
    | Formula.atom _ => f
    | Formula.scope vars quant inner => 
        match quant with
        | some q =>
            let normalized := if q.startsWith "_" then q.drop 1 else q
            dbg_trace s!"buildMinimalFormula examining scope with quant: {normalized}"
            if ["never_a_1", "neg"].contains normalized then
              dbg_trace s!"Preserving negation scope for {normalized} with vars {vars}"
              Formula.scope vars (some normalized) (buildMinimalFormula preds inner)
            else Formula.scope vars quant (buildMinimalFormula preds inner)
        | none => Formula.scope vars none (buildMinimalFormula preds inner)
    | _ =>
      dbg_trace s!"buildMinimalFormula starting with {preds.length} predicates"
      
      let baseState := preds.foldl (fun (state : FormulaState) (ep : EP) =>
        dbg_trace s!"Processing predicate: {ep}"
        let varsUsed := getXVars ep
        let newNeeded := varsUsed.filter (fun v => !state.declared.contains v)
        { state with
          neededVars := (state.neededVars ++ newNeeded).eraseDups,
          formula := Formula.conj (Formula.atom ep :: match state.formula with
            | Formula.conj fs => fs
            | f => [f]) }) { declared := [], neededVars := [], formula := Formula.conj [] }

      let scopes := getFormulaScopes f
      dbg_trace s!"Found scopes: {scopes}"
      
      let negScopes := scopes.filter fun si =>
        match si.scopeType with 
        | ScopeType.NeverNeg | ScopeType.RegNeg => true
        | _ => false
      dbg_trace s!"Found negation scopes: {negScopes}"
      
      let univVars := baseState.neededVars.filter (fun v =>
        scopes.any fun si => 
          match si.scopeType with
          | ScopeType.Universal => si.boundVars.contains v
          | _ => false)
      
      let defVars := baseState.neededVars.filter (fun v =>
        scopes.any fun si =>
          match si.scopeType with
          | ScopeType.Definite => si.boundVars.contains v
          | _ => false)

      let indefVars := baseState.neededVars.filter (fun v =>
        scopes.any fun si =>
          match si.scopeType with
          | ScopeType.Indefinite => si.boundVars.contains v
          | _ => false)

      let negVars := baseState.neededVars.filter (fun v =>
        scopes.any fun si =>
          match si.scopeType with
          | ScopeType.NeverNeg | ScopeType.RegNeg => si.boundVars.contains v
          | _ => false)

      dbg_trace s!"Variables by type - Universal:{univVars} Definite:{defVars} Indefinite:{indefVars} Negation:{negVars}"

      -- Group variables by their quantifier type
      let quantMap := scopes.foldl (fun map si =>
        si.boundVars.foldl (fun m v => 
          match m.find? v with
          | none => m.insert v si.predicate
          | some _ => m) map) HashMap.empty

      -- Group indefinite vars by quantifier
      let byQuant := indefVars.foldl (fun acc v =>
        match quantMap.find? v with
        | some quant =>
          match acc.find? quant with
          | some vars => acc.insert quant (v :: vars)
          | none => acc.insert quant [v]
        | none => acc) HashMap.empty

      -- Build formula preserving negation and combining scopes
      let withUniv := 
        if univVars.isEmpty then baseState.formula
        else combineScopes univVars "every_q" baseState.formula
      
      let withDef := 
        if defVars.isEmpty then withUniv
        else combineScopes defVars "the_q" withUniv

      -- Apply grouped indefinite scopes
      let withIndef := byQuant.toList.foldl (fun acc (quant, vars) =>
        combineScopes vars quant acc) withDef

      -- Apply negation scopes at the outermost level
      let withNeg := negScopes.foldl (fun acc scope =>
        match scope.negVar with
        | some var => Formula.scope [var] (some scope.predicate) acc
        | none => acc) withIndef

      dbg_trace s!"Final formula with negation: {withNeg}"
      withNeg

end

def minimizeScoping (f : Formula) : Formula :=
  dbg_trace "Starting minimizeScoping"
  dbg_trace s!"Input formula: {f}"
  let result := minimizeScopeRegion f
  dbg_trace s!"Output formula: {result}"
  result

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (minimizeScoping)
