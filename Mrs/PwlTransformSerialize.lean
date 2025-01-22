import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformFormat
import Mrs.PwlTransformLambdaRestructure_Types
import Mrs.Hof
import Util.InsertionSort
import Lean.Data.RBTree

namespace PWL.Transform

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open PWL.Transform.LambdaRestructure

open PWL.Transform.Format (
  formatPredArgs
  formatConjunction
  makeIndent
  varList_toString
  filterScopeVars
  FormatConfig
  normalizePredicate
  debugNested
  getNegComment
  formatWithGuardComments
  defaultConfig
)
open Lean

partial def lambdaContentInAtom (ep : EP) (targetVar : Var) 
    (lambdaVars : Lean.RBTree Var compare)
    (visitedPreds : List EP) : Option Formula :=
  if visitedPreds.contains ep then
    dbg_trace s!"FIND_LAMBDA_ATOM: skipping visited predicate {ep.predicate}"
    none
  else
    let arg0 := ep.rargs.find? (fun arg => arg.1 == "ARG0")
    let refArgs := ep.rargs.filter (fun arg => arg.1 != "ARG0" && arg.2.sort == 'x')

    dbg_trace s!"FIND_LAMBDA_ATOM: predicate={ep.predicate}"
    dbg_trace s!"FIND_LAMBDA_ATOM: args={ep.rargs}"
    dbg_trace s!"FIND_LAMBDA_ATOM: target={targetVar}"

    if isLambdaPredicate ep.predicate then
      match arg0 with
      | some (_, v) =>
        dbg_trace s!"FIND_LAMBDA_ATOM: found lambda output {v}"
        dbg_trace s!"FIND_LAMBDA_ATOM: found refs {refArgs}"
        if v == targetVar then 
          dbg_trace s!"FIND_LAMBDA_ATOM: matched target"
          some (Formula.atom ep)
        else 
          match refArgs.find? (fun ref => lambdaVars.contains ref.2 && ref.2 == targetVar) with
          | some _ =>
            dbg_trace s!"FIND_LAMBDA_ATOM: found lambda application of target {targetVar}"
            some (Formula.atom ep) 
          | none =>
            dbg_trace s!"FIND_LAMBDA_ATOM: no target match"
            none
      | none => 
        dbg_trace s!"FIND_LAMBDA_ATOM: no lambda output"
        none
    else
      dbg_trace s!"FIND_LAMBDA_ATOM: not a lambda predicate"
      none

mutual 
  partial def lambdaContentSerialize (f : Formula) (targetVar : Var) 
      (lambdaVars : Lean.RBTree Var compare)
      (visited : List (List Var × Option String))
      (visitedPreds : List EP)
      (visitedFormulas : List Formula) : Option Formula :=
    dbg_trace s!"FIND_SERIALIZE: examining formula for {targetVar}: {match f with 
      | Formula.scope vars _ _ => s!"scope[{vars}]"
      | Formula.conj fs => s!"conj({fs.length})"
      | Formula.atom ep => s!"atom({ep.predicate})"}"
    if visitedFormulas.contains f then
      dbg_trace s!"FIND_SERIALIZE: skipping already visited formula"
      none
    else
      let newVisited := f :: visitedFormulas
      match f with
      | Formula.atom ep => 
        dbg_trace s!"FIND_SERIALIZE: checking atom {ep.predicate}"
        lambdaContentInAtom ep targetVar lambdaVars visitedPreds
        
      | Formula.scope vars q inner =>
        dbg_trace s!"FIND_SERIALIZE: checking scope {vars} quant={q}"
        let scopeKey := (vars, q)
        if visited.contains scopeKey then 
          dbg_trace "FIND_SERIALIZE: scope already visited"
          none
        else
          match inner with
          | Formula.conj fs => 
            dbg_trace s!"FIND_SERIALIZE: processing scope conjunction with {fs.length} formulas"
            processInnerList targetVar lambdaVars fs vars q (scopeKey :: visited) visitedPreds newVisited
          | _ =>
            dbg_trace "FIND_SERIALIZE: recursing into non-conj inner scope"
            match lambdaContentSerialize inner targetVar lambdaVars (scopeKey :: visited) visitedPreds newVisited with
            | some content => 
              dbg_trace s!"FIND_SERIALIZE: found content in inner scope"
              some (Formula.scope vars q content)
            | none => none

      | Formula.conj fs => 
        dbg_trace s!"FIND_SERIALIZE: processing top-level conjunction with {fs.length} formulas"
        searchConjList targetVar lambdaVars fs visited visitedPreds newVisited []

  partial def processInnerList (targetVar : Var) (lambdaVars : Lean.RBTree Var compare)
      (fs : List Formula) (vars : List Var)
      (q : Option String) (visited : List (List Var × Option String))
      (visitedPreds : List EP) (visitedFormulas : List Formula) : Option Formula :=
    dbg_trace s!"PROC_INNER: target={targetVar} vars={vars} formulas={fs.length}"
    match fs with
    | [] => 
      dbg_trace "PROC_INNER: no formulas to process"
      none
    | f :: rest =>
      dbg_trace s!"PROC_INNER: processing first formula: {match f with
        | Formula.scope vs _ _ => s!"scope[{vs}]"
        | Formula.conj inner => s!"conj({inner.length})"
        | Formula.atom ep => s!"atom({ep.predicate})"}"
      match lambdaContentSerialize f targetVar lambdaVars visited visitedPreds visitedFormulas with
      | some result => 
        dbg_trace s!"PROC_INNER: found content in current formula"
        some (Formula.scope vars q (Formula.conj (result :: rest)))
      | none => 
        dbg_trace s!"PROC_INNER: no content in current formula, trying rest ({rest.length} remaining)"
        processInnerList targetVar lambdaVars rest vars q visited visitedPreds visitedFormulas

  partial def searchConjList (targetVar : Var) (lambdaVars : Lean.RBTree Var compare)
      (fs : List Formula)
      (visited : List (List Var × Option String))
      (visitedPreds : List EP)
      (visitedFormulas : List Formula)
      (acc : List Formula) : Option Formula :=
    dbg_trace s!"SEARCH_CONJ: target={targetVar} searching {fs.length} remaining formulas, have {acc.length} processed"
    match fs with
    | [] => 
      dbg_trace "SEARCH_CONJ: no more formulas to search"
      none 
    | f :: rest =>
      dbg_trace s!"SEARCH_CONJ: examining formula: {match f with
        | Formula.scope vars _ _ => s!"scope[{vars}]"
        | Formula.conj inner => s!"conj({inner.length})"
        | Formula.atom ep => s!"atom({ep.predicate})"}"
      match lambdaContentSerialize f targetVar lambdaVars visited visitedPreds visitedFormulas with 
      | some result => 
        dbg_trace s!"SEARCH_CONJ: found content, combining with {acc.length} accumulated and {rest.length} remaining"
        some (Formula.conj (acc ++ [result] ++ rest))
      | none => 
        dbg_trace s!"SEARCH_CONJ: no content found, adding to accumulated and continuing search"
        searchConjList targetVar lambdaVars rest visited visitedPreds visitedFormulas (acc ++ [f])
end

partial def formatAsPWL (f : Formula) (root : Formula) (lambdaVars : Lean.RBTree Var compare) 
   (bv : Option Var) (visitedFormulas : List Formula := [])
   (ind : Nat := 0) (inP : Bool := false) 
   (skipInitialIndent : Bool := false) (inNoQ : Bool := false) : String :=
  if visitedFormulas.contains f then
    dbg_trace "ASPLWL: skipping already visited formula"
    ""
  else
    let newVisited := f :: visitedFormulas
    let indentStr := if skipInitialIndent then "" else makeIndent ind
    match f with
    | Formula.atom ep =>
      if ep.predicate == "implicit_conj" || ep.predicate == "_implicit_conj" ||
         ep.predicate == "and_c" || ep.predicate == "_and_c" then
        if ep.rargs.all (fun arg => arg.2.sort == 'x') then
          match ep.rargs.find? (fun arg => arg.1 == "ARG0") with
          | some (_, output) =>
            if lambdaVars.contains output then
              match lambdaContentSerialize (Formula.atom ep) output lambdaVars [] [] newVisited with 
              | some content => formatAsPWL content root lambdaVars bv newVisited ind inP skipInitialIndent inNoQ
              | none => formatConjunction ep ind lambdaVars
            else formatConjunction ep ind lambdaVars
          | none => formatConjunction ep ind lambdaVars
        else formatPredArgs defaultConfig ep.predicate ep.rargs ep.carg ind inNoQ false
      else formatPredArgs defaultConfig ep.predicate ep.rargs ep.carg ind inNoQ false

    | Formula.scope vars none inner =>
      let filteredVars := filterScopeVars defaultConfig vars
      if vars.length == 1 && vars.head!.sort == 'q' && vars.head!.id == 0 then
        s!"{indentStr}^[{varList_toString filteredVars}]:(\n{formatAsPWL inner root lambdaVars bv newVisited (ind + 2) false false inNoQ})"
      else if filteredVars.isEmpty then
        formatAsPWL inner root lambdaVars bv newVisited ind inP skipInitialIndent inNoQ
      else
        s!"{indentStr}?[{varList_toString filteredVars}]:(\n{formatAsPWL inner root lambdaVars bv newVisited (ind + 2) false false inNoQ})"

    | Formula.scope vars (some q) inner =>
      let normalized := normalizePredicate q
      if normalized == "rstr_guard" || normalized == "body_guard" then
        formatAsPWL inner root lambdaVars bv newVisited ind inP skipInitialIndent inNoQ
      else if (normalized == "neg" || normalized == "never_a_1") && vars.isEmpty then
        s!"{makeIndent ind}~{getNegComment normalized}{formatAsPWL inner root lambdaVars bv newVisited ind false true true}"
      else
        match inner with
        | Formula.conj [rstr, body] =>
          let qtype := if normalized == "every_q" then "!" else "?"
          let qvar := vars.head!
          let rstrStr := formatAsPWL rstr root lambdaVars bv newVisited (ind + 2) false false false
          let bodyStr := formatAsPWL body root lambdaVars bv newVisited (ind + 2) false false false
          s!"{indentStr}{qtype}[{varList_toString vars}]:(/* {normalized} */\n{formatWithGuardComments rstrStr bodyStr qvar ind})"
        | _ =>
          let qtype := if normalized == "every_q" then "!" else "?"
          let filteredVars := filterScopeVars defaultConfig vars
          if filteredVars.isEmpty then
            formatAsPWL inner root lambdaVars bv newVisited ind false false false
          else
            let qvar := vars.head!
            let innerStr := formatAsPWL inner root lambdaVars bv newVisited (ind + 2) false false false
            s!"{indentStr}{qtype}[{varList_toString vars}]:(/* {normalized} */\n{makeIndent (ind + 2)}/* BODY[{qvar}] */\n{innerStr})"

    | Formula.conj [] => ""

    | Formula.conj [f] => formatAsPWL f root lambdaVars bv newVisited ind inP skipInitialIndent inNoQ

    | Formula.conj fs =>
      let nonEmpty := fs.filter (fun f => !f.isEmptyConj)
      String.intercalate " &\n" (nonEmpty.map (fun f => 
        formatAsPWL f root lambdaVars bv newVisited ind false false inNoQ))

end PWL.Transform

export PWL.Transform (formatAsPWL)
