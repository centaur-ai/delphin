import Mrs.Basic
import Mrs.PwlTypes 
import Mrs.PwlTransformShared
import Util.InsertionSort
import Lean.Data.RBTree

namespace PWL.Transform.LambdaRestructure

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open HOF
open Lean

inductive LambdaStatus where
  | KeepScope : LambdaStatus   -- Keep the scope introduction 
  | Obsolete  : LambdaStatus   -- Remove scope and definition
  deriving BEq, Inhabited

instance : ToString LambdaStatus where
  toString 
  | LambdaStatus.KeepScope => "keepScope"
  | LambdaStatus.Obsolete => "obsolete" 

/-- Information about a lambda variable and its content -/
structure LambdaInfo where
  sourceVar : Var         -- Variable bound to lambda
  targetVars : List Var   -- Variables referenced in lambda body
  predicate : String      -- Name of predicate (and_c or implicit_conj)
  bodyContent : Option Formula  -- Associated body predicates 
  status : LambdaStatus
  deriving Inhabited

instance : BEq LambdaInfo where
  beq a b := a.sourceVar == b.sourceVar && 
             a.targetVars == b.targetVars &&
             a.predicate == b.predicate &&
             a.bodyContent == b.bodyContent &&
             a.status == b.status

instance : ToString LambdaInfo where
  toString l := s!"{l.sourceVar} -> {l.targetVars} ({l.predicate}) [{l.status}]"

/-- Information about consolidated lambdas -/
structure LambdaConsolidation where
  targetVar : Var     -- Variable that gets consolidated lambda
  sources : List (Var × List Var)  -- Source lambdas and their vars
  scope : Option Var  -- Target scope
  bodyContent : Option Formula  -- Preserved predicates using this lambda
  preservedScopes : List Var   -- Scopes that must be kept
  quantifier : Option String   -- Optional quantifier type
  deriving Inhabited

instance : ToString LambdaConsolidation where
  toString c := s!"Consolidation({c.targetVar} <- {c.sources})"

/-- Information about where a variable is defined and used -/
structure ScopeInfo where
  definedVar : Var              -- Variable being defined
  definingScope : Option Var    -- Scope where it's defined (if any)  
  dependencies : List Var       -- Variables this one depends on
  usedInGuards : Bool          -- Whether used in RSTR/BODY guards
  deriving Inhabited, BEq

instance : ToString ScopeInfo where
  toString s := s!"ScopeInfo({s.definedVar}, scope={s.definingScope}, deps={s.dependencies}, guarded={s.usedInGuards})"

structure MovePlan where
  subtreeRoot : Var            
  fromScope : Option Var       
  toScope : Option Var        
  isGuarded : Bool            
  consolidatedLambda : Option Formula
  bodyContent : Option Formula
  path : List Var
  deriving Inhabited, BEq

instance : ToString MovePlan where
  toString m := s!"MovePlan({m.subtreeRoot}, bodyContent={match m.bodyContent with | none => "none" | some _ => "some"})"

instance [ToString α] : ToString (List α) where
  toString xs := "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

def isLambdaPredicate (p : String) : Bool :=
  dbg_trace s!"LAMBDA_PRED: checking {p}"
  let result := p == "and_c" || p == "_and_c" ||
                p == "implicit_conj" || p == "_implicit_conj"
  dbg_trace s!"LAMBDA_PRED: result={result}"
  result

def getOutArg (ep : EP) : Option Var :=
  ep.rargs.find? (fun arg => arg.1 == "ARG0")
  |>.map (fun arg => arg.2)

def getTargetVars (ep : EP) : List Var :=
  ep.rargs.filter (fun arg => arg.1 != "ARG0" && arg.2.sort == 'x')
  |>.map (·.2)

partial def containsAllTargets (lambdaA : LambdaInfo) (lambdaB : LambdaInfo) (lambdas : List LambdaInfo) : Bool :=
  let rec expandTargets (v : Var) : List Var :=
    match lambdas.find? (fun l => l.sourceVar == v) with
    | none => [v]
    | some info => 
      if info.status == LambdaStatus.KeepScope then
        [v]  -- Don't expand lambdas marked for scope keeping
      else
        info.targetVars.foldl (fun acc t => acc ++ expandTargets t) []
    
  let expandedA := lambdaA.targetVars.foldl (fun acc v => acc ++ expandTargets v) []
  let expandedB := lambdaB.targetVars.foldl (fun acc v => acc ++ expandTargets v) []
  
  expandedB.all fun target =>
    expandedA.any (· == target)

/-- State for tracking processing during tree restructuring -/
structure ProcessedState where
  inserted : List Var     -- Track variables we've already inserted
  visited : List Formula  -- Track formulas we've already visited
  processedScopes : List (Option Var) -- Track scopes we've handled
  deriving Inhabited

instance : ToString ProcessedState where
  toString s := s!"ProcessedState(inserted={s.inserted}, visited={s.visited.length} formulas, processedScopes={s.processedScopes})"

def ProcessedState.hasProcessed (state : ProcessedState) (scope : Option Var) : Bool :=
  state.processedScopes.contains scope

def ProcessedState.hasInserted (state : ProcessedState) (v : Var) : Bool :=
  state.inserted.contains v 

def ProcessedState.hasVisited (state : ProcessedState) (f : Formula) : Bool :=
  state.visited.contains f

/-- Check if quantifier is a guard -/
def isGuardQuant : Option String → Bool
  | some "rstr_guard" => true
  | some "body_guard" => true
  | _ => false

instance : ToString (HashSet Var) where
  toString s := toString (s.toArray.toList)

/-- State tracking for formula processing -/
structure ProcessState where
  processedVars : HashSet Var
  currentScope : Option Var
  deriving Inhabited

def ProcessState.init : ProcessState := {
  processedVars := HashSet.empty,
  currentScope := none
}

def ProcessState.markProcessed (state : ProcessState) (v : Var) : ProcessState :=
  { state with processedVars := state.processedVars.insert v }

def ProcessState.hasProcessed (state : ProcessState) (v : Var) : Bool :=
  state.processedVars.contains v

def ProcessState.setScope (state : ProcessState) (scope : Option Var) : ProcessState :=
  { state with currentScope := scope }

instance : ToString ProcessState where
  toString s := s!"ProcessState(processed={s.processedVars}, scope={s.currentScope})"

end PWL.Transform.LambdaRestructure

export PWL.Transform.LambdaRestructure (
  LambdaStatus
  LambdaInfo 
  LambdaConsolidation
  ScopeInfo
  MovePlan
  isLambdaPredicate
  getOutArg
  getTargetVars
  containsAllTargets
  isGuardQuant
  ProcessState
)
