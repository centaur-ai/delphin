import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared 

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
| ColonNamely    -- colon_p_namely
deriving Inhabited, BEq

instance : ToString ScopeType where
  toString 
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

def getScopeVars (ep : EP) : List Var :=
  dbg_trace s!"Extracting scopable variables from EP: {ep}"
  let mainVars := (ep.rargs.filter (fun arg => arg.2.sort == 'x' || arg.2.sort == 'e')
   |>.map (·.2))
  let eventVars := (ep.rargs.filter (fun arg => arg.2.sort == 'e')
   |>.map (·.2))
  (mainVars ++ eventVars).eraseDups

partial def getFormulaScopes : Formula → List ScopeInfo
| Formula.atom _ => []  
| Formula.conj fs => 
  match fs with
  | [] => []
  | _ => fs.foldl (fun acc f => acc ++ getFormulaScopes f) []
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
    else if normalized == "colon_p_namely" then
      dbg_trace s!"Found colon_p_namely scope with vars: {vars}"
      ScopeType.ColonNamely
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
            if ["never_a_1", "neg", "colon_p_namely"].contains normalized then
              dbg_trace s!"Preserving scope for {normalized} with vars {vars}"
              Formula.scope vars (some normalized) (buildMinimalFormula preds inner)
            else Formula.scope vars quant (buildMinimalFormula preds inner)
        | none => Formula.scope vars none (buildMinimalFormula preds inner)
    | _ =>
      dbg_trace s!"buildMinimalFormula starting with {preds.length} predicates"
      
      let baseState := preds.foldl (fun (state : FormulaState) (ep : EP) =>
        dbg_trace s!"Processing predicate: {ep}"
        let varsUsed := getScopeVars ep
        dbg_trace s!"Found variables: {varsUsed}"
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
        | ScopeType.NeverNeg | ScopeType.RegNeg | ScopeType.ColonNamely => true
        | _ => false
      dbg_trace s!"Found negation scopes: {negScopes}"
      
      let allVars := baseState.neededVars
      
      -- Split into entity and event variables
      let entityVars := allVars.filter (fun v => v.sort == 'x')
      let eventVars := allVars.filter (fun v => v.sort == 'e')

      -- Group entity variables by scope type
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

      let negVars := entityVars.filter (fun v =>
        scopes.any fun si =>
          match si.scopeType with
          | ScopeType.NeverNeg | ScopeType.RegNeg | ScopeType.ColonNamely => si.boundVars.contains v
          | _ => false)
          
      -- Add event variables at the outermost scope
      let withEvents := 
        if eventVars.isEmpty then baseState.formula
        else Formula.scope eventVars none baseState.formula

      -- Build formula while separating variables for one-to-one quantifier bindings
      let withUniv := univVars.foldl (fun acc v => Formula.scope [v] (some "every_q") acc) withEvents
      
      let withDef := defVars.foldl (fun acc v => Formula.scope [v] (some "the_q") acc) withUniv

      -- Group indefinite vars by quantifier to preserve their specific types
      let quantMap := scopes.foldl (fun map si =>
        si.boundVars.foldl (fun m v => 
          match m.find? v with
          | none => m.insert v si.predicate
          | some _ => m) map) HashMap.empty

      -- Create individual scopes for each indefinite variable
      let withIndef := indefVars.foldl (fun acc v =>
        match quantMap.find? v with
        | some quant => Formula.scope [v] (some quant) acc
        | none => acc) withDef

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
