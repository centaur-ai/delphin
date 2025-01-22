import Mrs.Basic
import Mrs.PwlTypes 
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Mrs.PwlTransformLambdaRestructure_TreeOps
import Mrs.PwlTransformLambdaRestructure_TreeOps_Scoping
import Mrs.Hof
import Util.InsertionSort
import Lean.Data.RBTree

namespace PWL.Transform.LambdaRestructure 

open MRS (Var EP)
open PWL.Transform
open PWL.Transform.MinScoping (getEventVars getNonEventVars)
open Lean (RBTree)

private structure FragmentPath where
  path : List Var
  ending : String
  formula : Option Formula := none
  deriving Inhabited

instance : ToString FragmentPath where
  toString p := 
    let fstr := match p.formula with
                | some f => s!", formula: {f}"
                | none => ""
    s!"path: {p.path}, ending: {p.ending}{fstr}"

instance : ToString (List FragmentPath) where
  toString ps := "[" ++ String.intercalate ", " (ps.map toString) ++ "]"

structure ScopeContext where
  currentScope : Option Var := none
  outerScopes : List (Option Var) := []
  processedVars : List Var := []
  ancestors : List Var := []
  lambdas : List (Var × List Var) := []
  deriving Inhabited

instance : ToString ScopeContext where
  toString sc := 
    let lambdasStr := sc.lambdas.map (fun (v,deps) => 
      toString v ++ ":[" ++ 
      (deps.map toString |> String.intercalate ",") ++ "]"
    ) |> String.intercalate "; "
    "ScopeContext(current=" ++ toString sc.currentScope ++ 
    ", outer=" ++ toString sc.outerScopes ++ 
    ", processed=" ++ toString sc.processedVars ++ 
    ", ancestors=" ++ toString sc.ancestors ++ 
    ", lambdas=" ++ lambdasStr ++ ")"

private partial def findEmptyPath (f : Formula) (curr : List Var) (lambdaDeps : List Var) 
    (inDeps : Bool) : List FragmentPath :=
  dbg_trace s!"EMPTY_PATH: Starting with curr={curr}, lambdaDeps={lambdaDeps}, inDeps={inDeps}"
  match f with
  | Formula.scope vars _ inner =>
    match vars.head? with
    | some scopeVar => 
      dbg_trace s!"EMPTY_PATH: Found scope {scopeVar}"
      let newInDeps := inDeps || lambdaDeps.contains scopeVar
      dbg_trace s!"EMPTY_PATH: Contains in lambdaDeps? {lambdaDeps.contains scopeVar}"
      let newPath := if newInDeps then curr ++ [scopeVar] else curr
      dbg_trace s!"EMPTY_PATH: New path={newPath}"
      match inner with
      | Formula.conj [] => 
        let pathStr := newPath.map toString |> String.intercalate " -> "
        dbg_trace s!"EMPTY_PATH: Found empty conjunction at {pathStr}"
        [{ path := newPath, ending := "HOLE", formula := none }]
      | Formula.conj fs => 
        let hasEmpty := fs.any (fun f => match f with 
          | Formula.conj [] => true 
          | _ => false)
        if hasEmpty && newInDeps then
          dbg_trace s!"EMPTY_PATH: Found empty conjunct with deps"
          [{ path := newPath, ending := "HOLE", formula := none }]
        else 
          dbg_trace s!"EMPTY_PATH: Recursing into inner"
          findEmptyPath inner newPath lambdaDeps newInDeps
      | _ => 
        dbg_trace s!"EMPTY_PATH: Recursing on non-conjunction"
        findEmptyPath inner newPath lambdaDeps newInDeps
    | none => 
      dbg_trace s!"EMPTY_PATH: No scopeVar, recursing"
      findEmptyPath inner curr lambdaDeps inDeps
  | Formula.atom _ => []
  | Formula.conj [] => 
    if inDeps then
      dbg_trace s!"EMPTY_PATH: Found empty conj with deps: path={curr}"
      [{ path := curr, ending := "HOLE", formula := none }] 
    else []
  | Formula.conj fs =>
    dbg_trace s!"EMPTY_PATH: Processing conjunction with {fs.length} formulas"
    fs.foldl (fun acc f => 
      acc ++ findEmptyPath f curr lambdaDeps inDeps) []

-- Also debug lambda path collection
private partial def findLambdaPath (f : Formula) (curr : List Var) : (List FragmentPath × List Var) :=
  dbg_trace s!"LAMBDA_PATH: Starting with curr={curr}"
  match f with 
  | Formula.atom ep =>
    if isLambdaPredicate ep.predicate then
      match getOutArg ep with 
      | some v =>
        let deps := ep.rargs.filter (fun arg => arg.1 != "ARG0" && arg.2.sort == 'x') |>.map (·.2)
        dbg_trace s!"LAMBDA_PATH: Found lambda {ep.predicate} with var={v} deps={deps}"
        ([{ path := curr, 
            ending := s!"{ep.predicate}({v},{deps})", 
            formula := some (Formula.atom ep) }], deps)
      | none => ([], [])
    else ([], [])
  | Formula.scope vars _ inner =>
    match vars.head? with 
    | some scopeVar =>
      dbg_trace s!"LAMBDA_PATH: Found scope {scopeVar}"
      let (paths, deps) := findLambdaPath inner (curr ++ [scopeVar])
      dbg_trace s!"LAMBDA_PATH: After scope {scopeVar}, paths={paths}, deps={deps}"
      (paths, deps)
    | none => findLambdaPath inner curr
  | Formula.conj fs =>
    dbg_trace s!"LAMBDA_PATH: Processing conjunction"
    fs.foldl (fun (acc, deps) f =>
      let (paths, newDeps) := findLambdaPath f curr
      dbg_trace s!"LAMBDA_PATH: Conjunct gave paths={paths} deps={deps ++ newDeps}"
      (acc ++ paths, deps ++ newDeps)) ([], [])

private partial def collectFragmentPath (f : Formula) : (List FragmentPath × List FragmentPath) :=
  let (lambdaPaths, lambdaDeps) := findLambdaPath f []
  let holePaths := findEmptyPath f [] lambdaDeps false
  
  let lambdaStr := lambdaPaths.map toString |> String.intercalate "\n    "
  let holeStr := holePaths.map toString |> String.intercalate "\n    "
  dbg_trace s!"Fragment paths:\n  Lambda paths:\n    {lambdaStr}\n  Hole paths:\n    {holeStr}"
  
  (holePaths, lambdaPaths)

def formatFragmentPaths (f : Formula) : List String :=
  match collectFragmentPath f with 
  | (holePaths, lambdaPaths) => 
    (holePaths ++ lambdaPaths).map (fun path =>
      let pathStr := path.path.map toString |> String.intercalate " -> "
      "FRAGMENT_PATH: " ++ pathStr ++ " -> " ++ path.ending)

partial def analyzeScopedVars (f : Formula) : ScopeContext := 
  let rec analyze (acc : ScopeContext) (f : Formula) : ScopeContext :=
    match f with
    | Formula.scope vars _ inner =>
      let varsStr := vars.map toString |> String.intercalate ", "
      dbg_trace s!"Processing scope with vars {varsStr}"
      let nextCtx := { currentScope := vars.head?
                     , outerScopes := acc.currentScope :: acc.outerScopes
                     , processedVars := acc.processedVars ++ vars
                     , ancestors := acc.ancestors ++ (vars.filter (·.sort == 'x'))
                     , lambdas := acc.lambdas }
      analyze nextCtx inner
        
    | Formula.conj fs =>
      dbg_trace s!"Processing conjunction with {fs.length} formulas"
      fs.foldl analyze acc

    | Formula.atom ep =>
      if isLambdaPredicate ep.predicate then
        let deps := ep.rargs.filter (fun arg => 
          arg.2.sort == 'x' && arg.1 != "ARG0") |>.map (·.2)
        match getOutArg ep with
        | some outVar =>
          let depsStr := deps.map toString |> String.intercalate ", "
          dbg_trace s!"Found lambda {ep.predicate} with output={outVar}, deps={depsStr}"
          { currentScope := acc.currentScope
          , outerScopes := acc.outerScopes
          , processedVars := acc.processedVars
          , ancestors := acc.ancestors
          , lambdas := (outVar, deps) :: acc.lambdas }
        | none => acc
      else acc

  analyze { currentScope := none
          , outerScopes := []
          , processedVars := []
          , ancestors := []
          , lambdas := [] } f

structure MoveConfig where
  enableLambdaMoves : Bool := true
  deriving Inhabited

partial def findBodyContent (f : Formula) (targetVar : Var) : Option Formula :=
  match f with 
  | Formula.scope vars quant inner =>
    dbg_trace s!"FIND_BODY: checking scope vars={vars}, quant={quant}"
    if vars.contains targetVar then
      dbg_trace s!"FIND_BODY: Found matching var {targetVar}" 
      match quant with
      | some "body_guard" =>
        dbg_trace s!"FIND_BODY: Found body content for {targetVar}: {inner}"
        some inner
      | _ =>
        findBodyContent inner targetVar
    else
      findBodyContent inner targetVar

  | Formula.conj fs =>
    fs.foldl (fun acc f => 
      match acc with
      | some content => some content  
      | none => findBodyContent f targetVar) none

  | Formula.atom _ => none

def defaultMoveConfig : MoveConfig := MoveConfig.mk true 
def scopeOnlyConfig : MoveConfig := MoveConfig.mk false

def planMoves (f : Formula) (scopes : ScopeContext) (cfg : MoveConfig := defaultMoveConfig) : List MovePlan :=  
  dbg_trace "MOVE_PLAN: Starting move planning"
  
  let (holePaths, lambdaPaths) := collectFragmentPath f

  -- Plan regular scope move 
  let scopeMoves := match holePaths.head? with
    | some hole =>
      match lambdaPaths.head? with
      | some lambda =>
        match hole.path.head? with
        | some moveVar =>
          match lambda.path.get? (lambda.path.length - 1) with
          | some targetVar =>
            dbg_trace "MOVE_PLAN: ==========================================="
            dbg_trace "MOVE_PLAN: SCOPE MOVE:"
            dbg_trace s!"MOVE_PLAN:   WHAT: Moving scope with pre-existing hole"
            dbg_trace s!"MOVE_PLAN:   FROM: {moveVar}"
            dbg_trace s!"MOVE_PLAN:   TO: {targetVar} BODY"
            dbg_trace s!"MOVE_PLAN:   PATH: {lambda.path}"
            dbg_trace "MOVE_PLAN: ==========================================="
            [MovePlan.mk moveVar none (some targetVar) false none none lambda.path]
          | none => []
        | none => []
      | none => []
    | none => []

  -- Plan lambda consolidation moves, controlled by config
  let lambdaMoves := if !cfg.enableLambdaMoves then []
    else match (holePaths.head?, lambdaPaths.head?) with
      | (some hole, some lambda) =>
        match lambda.formula with 
        | some f =>
          match f with
          | Formula.atom ep =>
            match getOutArg ep with
            | some lambdaVar =>
              match findBodyContent f lambdaVar with
              | some bodyContent =>
                match hole.path.getLast? with
                | some targetVar =>
                  dbg_trace "MOVE_PLAN: ==========================================="
                  dbg_trace "MOVE_PLAN: LAMBDA MOVE:"
                  dbg_trace s!"MOVE_PLAN:   WHAT: Moving consolidated lambda definition" 
                  dbg_trace s!"MOVE_PLAN:   INTO: Pre-existing hole in {targetVar} BODY"
                  dbg_trace s!"MOVE_PLAN:   Lambda path: {lambda.path}"
                  dbg_trace s!"MOVE_PLAN:   Hole path: {hole.path}"
                  let argList := ep.rargs.map (fun pair => toString pair.2)
                  dbg_trace s!"MOVE_PLAN:   LAMBDA: {ep.predicate}({String.intercalate ", " argList})"
                  dbg_trace s!"MOVE_PLAN:   Current hole: {hole.ending}"
                  dbg_trace s!"MOVE_PLAN:   Current lambda: {lambda.ending}"
                  dbg_trace s!"MOVE_PLAN:   Found body content: {bodyContent}"
                  dbg_trace "MOVE_PLAN: ==========================================="
                  [MovePlan.mk lambdaVar (some lambdaVar) (some targetVar) true (some f) (some bodyContent) hole.path]
                | none => []
              | none =>
                dbg_trace s!"MOVE_PLAN: No body content found for {lambdaVar}"
                []
            | none => []
          | _ => []
        | none => []
      | _ => []

  dbg_trace "MOVE_PLAN: Final moves:"
  dbg_trace s!"MOVE_PLAN:   Scope moves: {scopeMoves}"
  dbg_trace s!"MOVE_PLAN:   Lambda moves: {lambdaMoves}"

  lambdaMoves ++ scopeMoves

def adjustScopes (f : Formula) (moves : List MovePlan) : Formula := 
  let rec applyMoves (remaining : List MovePlan) (acc : Formula) (state : ProcessState) : Formula :=
    match remaining with
    | [] => 
      dbg_trace "ADJUST: No more moves to process"
      dbg_trace s!"ADJUST: Final formula:\n{acc}"
      acc
    | move :: rest =>
      dbg_trace s!"ADJUST: Processing {if move.consolidatedLambda.isSome then "LAMBDA" else "SCOPE"} move for {move.subtreeRoot}"
      dbg_trace s!"ADJUST: Formula tree BEFORE {if move.consolidatedLambda.isSome then "LAMBDA" else "SCOPE"} move:\n{acc}"

      match extractSubtree acc move.subtreeRoot state with 
      | none => 
        dbg_trace s!"ADJUST: Failed to extract {move.subtreeRoot}"
        dbg_trace s!"ADJUST: Continuing with unchanged formula:\n{acc}"
        applyMoves rest acc state
      | some (formulaWithHole, fragment, newState) =>
        dbg_trace s!"ADJUST: Successfully extracted {move.subtreeRoot}"
        dbg_trace s!"ADJUST: Extracted fragment:\n{fragment}"
        dbg_trace s!"ADJUST: Formula with hole:\n{formulaWithHole}"

        -- Update MovePlan if we found a lambda definition
        let updatedMove := match fragment with
        | Formula.atom ep =>
          if ep.predicate == "implicit_conj" || ep.predicate == "_implicit_conj" then
            dbg_trace s!"ADJUST: Found lambda definition, updating move plan"
            {move with consolidatedLambda := some fragment}
          else
            move
        | _ => move
        
        let (newF, _) := insertRec formulaWithHole none none updatedMove fragment false
        let finalState := newState

        dbg_trace s!"ADJUST: After insertion attempt:"
        dbg_trace s!"ADJUST: Formula tree AFTER {if move.consolidatedLambda.isSome then "LAMBDA" else "SCOPE"} move:\n{newF}"
        dbg_trace s!"ADJUST: Insertion state: {finalState}"
        dbg_trace s!"ADJUST: Formula {if newF == formulaWithHole then "was NOT" else "was"} modified by insertion"

        let nextAcc := applyMoves rest newF finalState
        dbg_trace s!"ADJUST: After processing remaining moves:\n{nextAcc}"
        nextAcc

  applyMoves moves f ProcessState.init

end PWL.Transform.LambdaRestructure

export PWL.Transform.LambdaRestructure (analyzeScopedVars planMoves adjustScopes formatFragmentPaths)

