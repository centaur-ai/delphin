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
| Formula.neg _ inner => getPredicatesFromFormula inner

def getXVars (ep : EP) : List Var :=
  dbg_trace s!"Extracting x-variables from EP: {ep}"
  (ep.rargs.filter (·.2.sort == 'x')
   |>.map (·.2)
   |>.eraseDups)

def isNegationBoundary : Formula → Bool
| Formula.neg _ _ => true
| _ => false

partial def getFormulaScopes : Formula → List ScopeInfo
| Formula.atom _ => []  
| Formula.conj fs => 
  match fs with
  | [] => []
  | _ => fs.foldl (fun acc f => acc ++ getFormulaScopes f) []
| Formula.scope vars (some pred) inner => 
  let scopeType := 
    if pred == "every_q" then
      ScopeType.Universal 
    else if pred == "the_q" || pred == "def_explicit_q" then
      ScopeType.Definite
    else
      ScopeType.Indefinite
  { predicate := pred,
    boundVars := vars.eraseDups,
    scopeType := scopeType } :: getFormulaScopes inner
| Formula.scope _ none inner => getFormulaScopes inner 
| Formula.neg negType inner =>
  let info : ScopeInfo := 
    { predicate := 
        match negType with
        | NegationType.Never _ => "never_a_1"
        | NegationType.NegWithEvent _ => "neg",
      boundVars := [],
      scopeType := 
        match negType with
        | NegationType.Never _ => ScopeType.NeverNeg
        | NegationType.NegWithEvent _ => ScopeType.RegNeg,
      negVar := 
        match negType with
        | NegationType.Never i => some i
        | NegationType.NegWithEvent e => some e }
  info :: getFormulaScopes inner

mutual

partial def combineScopes (vars : List Var) (quant : String) (inner : Formula) : Formula :=
  match vars with
  | [] => inner
  | _ => Formula.scope vars (some quant) inner

partial def minimizeScopeRegion (f : Formula) : Formula :=
  match f with
  | Formula.atom _ => f
  | Formula.conj fs => 
      let preds := getPredicatesFromFormula f
      buildMinimalFormula preds f
  | Formula.neg negType inner =>
      Formula.neg negType (minimizeScopeRegion inner)
  | Formula.scope vars quant inner =>
      Formula.scope vars quant (minimizeScopeRegion inner)

partial def preserveNegationScope (f : Formula) : Formula :=
  match f with
  | Formula.conj fs => Formula.conj (fs.map preserveNegationScope)
  | Formula.neg nt inner => Formula.neg nt (minimizeScopeRegion inner)
  | f => f

partial def buildMinimalFormula (preds : List EP) (f : Formula) : Formula := 
  match f with
  | Formula.atom _ => f
  | Formula.neg negType inner =>
    Formula.neg negType (buildMinimalFormula (getPredicatesFromFormula inner) inner)
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

    dbg_trace s!"Variables by type - Universal:{univVars} Definite:{defVars} Indefinite:{indefVars}"

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

    -- Build formula preserving negation boundaries and combining scopes
    let withUniv := 
      if univVars.isEmpty then baseState.formula
      else combineScopes univVars "every_q" baseState.formula
    
    let withDef := 
      if defVars.isEmpty then withUniv
      else combineScopes defVars "the_q" withUniv

    -- Apply grouped indefinite scopes
    let withIndef := byQuant.toList.foldl (fun acc (quant, vars) =>
      if isNegationBoundary acc then preserveNegationScope acc
      else combineScopes vars quant acc) withDef

    dbg_trace s!"Final formula: {withIndef}"
    withIndef

end

def minimizeScoping (f : Formula) : Formula :=
  dbg_trace "Starting minimizeScoping"
  minimizeScopeRegion f

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (minimizeScoping)
