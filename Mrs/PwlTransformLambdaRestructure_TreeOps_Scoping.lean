import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformLambdaRestructure_Types
import Mrs.PwlTransformFormat
import Mrs.PwlTransformSerialize
import Mrs.Hof
import Util.InsertionSort
import Lean.Data.RBTree
import Lean.Data.HashSet

namespace PWL.Transform.LambdaRestructure

open MRS (Var EP)
open PWL.Transform
open HOF
open Lean

/-- Check if a formula uses a specific variable -/
partial def formulaUsesVar (f : Formula) (targetVar : Var) : Bool :=
  match f with 
  | Formula.atom ep =>
    ep.rargs.any fun arg => arg.2 == targetVar

  | Formula.scope vars q inner =>
    if vars.contains targetVar then true
    else formulaUsesVar inner targetVar

  | Formula.conj fs => 
    fs.any (formulaUsesVar · targetVar)

/-- Debug helper to show formula type -/
def debugNested (f : Formula) : String :=
  match f with
  | Formula.atom ep => s!"atom({ep.predicate})"
  | Formula.scope vars _ _ => s!"scope(vars={vars})"
  | Formula.conj fs => s!"conj(len={fs.length})"

/-- Extract a subtree from a formula at a given root -/
partial def extractSubtree (f : Formula) (targetRoot : Var) (state : ProcessState) 
    : Option (Formula × Formula × ProcessState) :=
  dbg_trace s!"TREE.EXTRACT: Starting extraction for {targetRoot}"
  dbg_trace s!"TREE.EXTRACT: From formula:\n{f}"

  if state.hasProcessed targetRoot then
    dbg_trace s!"TREE.EXTRACT: {targetRoot} already processed, skipping extraction"
    none 
  else
    let rec extract (f : Formula) (inGuard : Bool) (depth : Nat)
                   (path : List String) (curState : ProcessState) 
        : Option (Formula × Formula × ProcessState) :=
      let indent := String.mk (List.replicate (depth * 2) ' ')
      let curPath := toString path.length
      
      dbg_trace s!"{indent}TREE.EXTRACT[{depth}][path={curPath}]: visiting formula: {debugNested f}"
      
      match f with
      | Formula.scope vars quant inner =>
        if vars.contains targetRoot then
          -- When we find target root's scope, save lambda if present
          match inner with 
          | Formula.atom ep =>
            if ep.predicate == "implicit_conj" || ep.predicate == "_implicit_conj" then
              dbg_trace s!"TREE.EXTRACT: Found implicit_conj definition in {targetRoot} scope"
              -- Return the lambda definition rather than the scope
              let lambda := Formula.atom ep
              some (Formula.conj [], lambda, curState.markProcessed targetRoot)
            else 
              dbg_trace s!"TREE.EXTRACT: Found scope for {targetRoot}"
              some (Formula.conj [], f, curState.markProcessed targetRoot)
          | _ =>
            dbg_trace s!"TREE.EXTRACT: Found scope for {targetRoot}"
            some (Formula.conj [], f, curState.markProcessed targetRoot)
        else
          let nextInGuard := inGuard || isGuardQuant quant
          match extract inner nextInGuard (depth + 1) (s!"scope[{vars}][{quant}]" :: path) curState with
          | none => none  
          | some (holeFormula, fragment, newState) =>
            -- Always preserve scope structure by wrapping hole in original scope
            some (Formula.scope vars quant holeFormula, fragment, newState)
            
      | Formula.conj fs => 
        let containingFormulas := fs.filter (fun f => formulaUsesVar f targetRoot)
        dbg_trace s!"{indent}TREE.EXTRACT[{depth}][path={curPath}]: found in {containingFormulas.length} conjuncts"
        
        let rec processConjuncts (remaining : List Formula) (acc : List Formula) : Option (Formula × Formula × ProcessState) := 
          match remaining with
          | [] => none
          | f::rest =>
            match extract f inGuard (depth + 1) (s!"conj[{fs.length}]" :: path) curState with 
            | some (holeFormula, fragment, newState) => 
              dbg_trace s!"{indent}TREE.EXTRACT[{depth}][path={curPath}]: found in conjunct"
              some (Formula.conj (acc ++ [holeFormula] ++ rest), fragment, newState)
            | none => processConjuncts rest (acc ++ [f])

        processConjuncts fs []

      | Formula.atom ep => none -- Only extract at scope level when finding target root

    extract f false 0 [] state

partial def insertRec (f : Formula) (parentScope : Option Var) (curScope : Option Var)
  (movePlan : MovePlan) (subtreeFormula : Formula) (hasModified : Bool := false)
  : (Formula × Bool) :=
  dbg_trace s!"INSERTREC: At parent={parentScope}, current={curScope}"
  
  if hasModified then
    (f, true) 
  else
    match f with
    | Formula.scope vars quant inner =>
      -- Update current scope based on vars
      let nextScope := match vars with
         | [] => curScope  -- Keep current for empty var lists
         | v::_ => some v  -- Take first var as new scope
      dbg_trace s!"INSERTREC: Found scope, vars={vars}, quant={quant}, nextScope={nextScope}"

      match quant with  
      | some "rstr_guard" =>
        dbg_trace s!"INSERTREC: In RSTR guard with curScope={nextScope}, toScope={movePlan.toScope}"
        if vars.isEmpty && nextScope == movePlan.toScope then
          match movePlan.consolidatedLambda with
          | some lambda =>
            dbg_trace s!"INSERTREC: Found RSTR guard for {nextScope}, adding implicit_conj"
            (Formula.scope [] (some "rstr_guard") (Formula.conj [inner, lambda]), true)
          | none => (f, hasModified)
        else
          let (newInner, modified) := insertRec inner curScope nextScope movePlan subtreeFormula hasModified
          (Formula.scope vars (some "rstr_guard") newInner, modified)

      | some "body_guard" => 
        dbg_trace s!"INSERTREC: In BODY guard with curScope={nextScope}, toScope={movePlan.toScope}, subtreeRoot={movePlan.subtreeRoot}"
        if vars.isEmpty && nextScope == movePlan.toScope then
          match movePlan.bodyContent with
          | some content =>
            dbg_trace s!"INSERTREC: Inserting body content into {nextScope}'s guard: {content}"
            (Formula.scope vars (some "body_guard") content, true)
          | none =>
            dbg_trace "INSERTREC: No body content to insert"
            (f, hasModified)
        else
          let (newInner, modified) := insertRec inner curScope nextScope movePlan subtreeFormula hasModified
          (Formula.scope vars (some "body_guard") newInner, modified)

      | some other => 
        dbg_trace s!"INSERTREC: Other quantifier: {other}"
        let (newInner, modified) := insertRec inner curScope nextScope movePlan subtreeFormula hasModified
        (Formula.scope vars quant newInner, modified)

      | none =>
        dbg_trace "INSERTREC: No quantifier"
        let (newInner, modified) := insertRec inner curScope nextScope movePlan subtreeFormula hasModified
        (Formula.scope vars none newInner, modified)

    | Formula.conj fs =>
      dbg_trace s!"INSERTREC: Processing conjunction with {fs.length} formulas"
      let rec processFormulas (remaining : List Formula) (acc : List Formula) (hadModification : Bool) : (List Formula × Bool) :=
        match remaining with
        | [] => (acc.reverse, hadModification)
        | f :: rest =>
          if !hadModification then
            let (newF, modified) := insertRec f parentScope curScope movePlan subtreeFormula false
            processFormulas rest (newF :: acc) modified
          else
            processFormulas rest (f :: acc) true

      let (processed, modified) := processFormulas fs [] false
      (Formula.conj processed, modified)

    | Formula.atom ep => 
      dbg_trace s!"INSERTREC: Found atom {ep.predicate}"
      (f, hasModified)

end PWL.Transform.LambdaRestructure

export PWL.Transform.LambdaRestructure (
  insertRec 
  extractSubtree
)
