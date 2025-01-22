import Mrs.Basic
import Mrs.PwlTypes 
import Mrs.PwlTransformShared
import Mrs.PwlTransformLambdaRestructure_Types
import Mrs.Hof
import Util.InsertionSort
import Lean.Data.RBTree

namespace PWL.Transform.LambdaRestructure

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open HOF
open Lean

def buildConsolidatedLambda (targetVar : Var) (allVars : List Var) : Formula :=
  dbg_trace s!"LAMBDA_BUILD: Creating consolidated lambda for {targetVar} with vars {allVars}"
  
  -- Build disjunction of equalities for each target variable
  let varRefs := allVars.map (fun v => s!"x={v}")
  let disjunction := String.intercalate " | " varRefs
  
  -- Create full lambda formula
  Formula.atom {
    predicate := "implicit_conj",
    label := targetVar,
    rargs := ("ARG0", targetVar) :: 
      (allVars.enum.map fun (i, v) => (s!"ARG{i+1}", v)),
    carg := some s!"/* implicit_conj */ \n        {disjunction}",
    link := none
  }

partial def processFormula (f : Formula) (obsoleteVars : List Var) (consolidation : Formula) 
    (targetVar : Var) (consolidatedVars : List Var := []) : Formula := 
  dbg_trace "PROCESS: Starting processFormula"
  dbg_trace s!"PROCESS: Will remove obsolete vars: {obsoleteVars}"
  dbg_trace s!"PROCESS: Target variable for consolidation: {targetVar}" 
  dbg_trace s!"PROCESS: Consolidated variables: {consolidatedVars}"
  
  let rec processFormulaImpl (f : Formula) (depth : Nat) : Formula :=
    let indent := String.mk (List.replicate (depth * 2) ' ')
    
    match f with
    | Formula.atom ep =>
      if isLambdaPredicate ep.predicate then
        match getOutArg ep with
        | some outVar =>
          if obsoleteVars.contains outVar then
            dbg_trace s!"PROCESS: Removing obsolete lambda for {outVar}"
            Formula.conj []
          else if outVar == targetVar then
            dbg_trace s!"PROCESS: Found lambda definition for target {targetVar}"
            dbg_trace s!"PROCESS: Original lambda: {ep}"
            dbg_trace s!"PROCESS: Replacing with consolidated lambda: {consolidation}"
            consolidation 
          else Formula.atom ep
        | none => Formula.atom ep
      else Formula.atom ep

    | Formula.scope vars q inner =>
      if vars.length == 1 && vars.head! == targetVar then
        dbg_trace s!"PROCESS: Processing scope for target {targetVar} with quantifier {q}"  
        let newInner := processFormulaImpl inner (depth + 1)
        let result := Formula.scope vars q newInner 
        dbg_trace s!"PROCESS: Completed scope for {targetVar} with result: {result}"
        result
      else if vars.length == 1 then
        let scopeVar := vars.head!
        if obsoleteVars.contains scopeVar then
          dbg_trace s!"PROCESS: Removing obsolete scope for {scopeVar}"
          processFormulaImpl inner (depth + 1)
        else
          dbg_trace s!"PROCESS: Preserving scope for {scopeVar}"
          Formula.scope vars q (processFormulaImpl inner (depth + 1))
      else
        Formula.scope vars q (processFormulaImpl inner (depth + 1))

    | Formula.conj fs =>
      let processed := fs.map (fun f => processFormulaImpl f (depth + 1))
      let nonEmpty := processed.filter (fun f => !f.isEmptyConj)
      match nonEmpty with
      | [] => Formula.conj []
      | [single] => single 
      | multiple => Formula.conj multiple

  processFormulaImpl f 0

/-- Remove obsolete lambda definitions from formula tree -/
partial def removeObsoleteLambdas (f : Formula) (obsoleteVars : List Var) : Formula :=
  dbg_trace s!"REMOVE: Starting with obsolete vars: {obsoleteVars}"
  
  let rec remove (f : Formula) (depth : Nat) : Formula :=
    match f with
    | Formula.scope vars q inner =>
      if vars.length == 1 && 
         -- Only remove scope if it's exactly for the obsolete lambda definition
         obsoleteVars.contains vars.head! && 
         q.isSome && 
         q.get!.endsWith "_q" &&
         -- Check if this scope directly contains the lambda definition
         match inner with
         | Formula.atom ep => 
           isLambdaPredicate ep.predicate && 
           match getOutArg ep with
           | some v => v == vars.head! 
           | none => false
         | _ => false then
        dbg_trace s!"REMOVE[{depth}]: Removing scope for obsolete lambda {vars.head!}"
        remove inner (depth + 1)
      else
        dbg_trace s!"REMOVE[{depth}]: Preserving scope {vars}"
        Formula.scope vars q (remove inner (depth + 1))
        
    | Formula.conj fs =>
      dbg_trace s!"REMOVE[{depth}]: Processing conjunction"
      let processed := fs.map (fun f' => remove f' (depth + 1))
      let nonEmpty := processed.filter (fun f' => !f'.isEmptyConj)
      if nonEmpty.isEmpty then Formula.conj []
      else Formula.conj nonEmpty
      
    | Formula.atom ep =>
      if isLambdaPredicate ep.predicate then
        match getOutArg ep with
        | some v =>
          if obsoleteVars.contains v then
            dbg_trace s!"REMOVE[{depth}]: Removing obsolete lambda {ep.predicate} for {v}"
            Formula.conj []
          else 
            dbg_trace s!"REMOVE[{depth}]: Keeping lambda {ep.predicate} for {v}"
            Formula.atom ep
        | none => Formula.atom ep
      else Formula.atom ep

  remove f 0

def insertConsolidatedAt (f : Formula) (targetVar : Var) (allVars : List Var) (obsoleteVars : List Var) : Formula :=
  dbg_trace s!"INSERT: Starting for target {targetVar}"
  
  -- Build consolidated lambda
  let lambda := buildConsolidatedLambda targetVar allVars

  -- Process formula to replace all instances and preserve scoping
  processFormula f obsoleteVars lambda targetVar (allVars.filter (fun v => !(obsoleteVars.contains v)))

end PWL.Transform.LambdaRestructure

export PWL.Transform.LambdaRestructure (
  buildConsolidatedLambda
  removeObsoleteLambdas
  insertConsolidatedAt
  processFormula
)
