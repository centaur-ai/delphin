import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Util.InsertionSort

namespace PWL.Transform.Serialize

open MRS (EP Var)
open PWL.Transform
open InsertionSort
open BEq

open PWL (removeQuotes)

structure FormatState where
  indent : Nat := 0

def addIndent (state : FormatState) : FormatState :=
  { state with indent := state.indent + 2 }

def getIndentStr (state : FormatState) : String :=
  String.mk (List.replicate state.indent ' ')

def normalizePredicate (pred : String) : String :=
  if pred.startsWith "_" then pred.drop 1 else pred

def varList_toString (vars : List Var) : String :=
  String.intercalate "," (vars.map toString)

def formatPredArgs (pred : String) (args : List (String × Var)) (carg : Option String) : String :=
  if pred == "named" || pred == "_named" then
    match args.find? (fun p => p.1 == "ARG0"), carg with
    | some (_, var), some str => 
      s!"name(n) & arg1(n)={var} & arg2(n)={str}"
    | _, _ => s!"named({args.head!.2})"
  else
    let orderedArgs := orderArgs args
    let firstEvent := orderedArgs.find? (fun a => a.2.sort == 'e')
    
    match firstEvent, orderedArgs with
    | none, [] => pred
    | none, (firstArg :: restArgs) =>
      let base := s!"{pred}({firstArg.2})"
      if restArgs.isEmpty then base
      else
        let argStr := restArgs.foldl (fun (acc : String × Nat) (pair : String × Var) =>
          let argNum := acc.2
          let str := if acc.1.isEmpty 
            then s!"arg{argNum}({firstArg.2})={pair.2}"
            else acc.1 ++ " & " ++ s!"arg{argNum}({firstArg.2})={pair.2}"
          (str, argNum + 1)
        ) ("", 1)
        s!"({base} & {argStr.1})"
    | some eventArg, _ =>
      let otherArgs := orderedArgs.filter (fun a => a != eventArg)
      let base := s!"{pred}({eventArg.2})"
      if otherArgs.isEmpty then base
      else
        let argStr := otherArgs.foldl (fun (acc : String × Nat) (pair : String × Var) =>
          let argNum := acc.2
          let str := if acc.1.isEmpty 
            then s!"arg{argNum}({eventArg.2})={pair.2}"
            else acc.1 ++ " & " ++ s!"arg{argNum}({eventArg.2})={pair.2}"
          (str, argNum + 1)
        ) ("", 1)
        s!"({base} & {argStr.1})"

mutual 

partial def formatAsPWLHelper : Formula → FormatState → String
  | Formula.scope vars (some q) inner, state =>
    let indent := getIndentStr state
    let nextState := addIndent state
    let normalizedQuant := normalizePredicate q
    match normalizedQuant with
    | "every_q" =>
      s!"{indent}![{vars.head!}]:(/* every_q */\n{formatAsPWLHelper inner nextState})"
    | "never_a_1" | "neg" | "colon_p_namely" =>
      let var := vars.head!
      if normalizedQuant == "colon_p_namely" then
        match inner with
        | Formula.conj [f1, f2] =>
          s!"{indent}((colon_p_namely({var}) &\n{formatAsPWLHelper f1 nextState} &\n{formatAsPWLHelper f2 nextState}))"
        | _ => s!"{indent}((colon_p_namely({var}) &\n{formatAsPWLHelper inner nextState}))"
      else
        s!"{indent}~(/* {normalizedQuant}({var}) */\n{formatAsPWLHelper inner nextState})"
    | _ =>
      s!"{indent}?[{vars.head!}]:(/* {normalizedQuant} */\n{formatAsPWLHelper inner nextState})"

  | Formula.scope vars none inner, state =>
    let indent := getIndentStr state
    let nextState := addIndent state
    if vars.all (fun v => v.sort == 'e') then
      formatEventGroup vars inner state
    else
      s!"{indent}?[{varList_toString vars}]:(\n{formatAsPWLHelper inner nextState})"

  | Formula.atom ep, state =>
    let indent := getIndentStr state
    s!"{indent}{formatPredArgs ep.predicate ep.rargs ep.carg}"

  | Formula.conj [], _ => ""
  | Formula.conj [f], state => formatAsPWLHelper f state
  | Formula.conj fs, state =>
    let nonEmpty := fs.filter (fun f => !f.isEmptyConj)
    match nonEmpty with
    | [] => ""
    | fs => String.intercalate " &\n" (fs.map (fun f => formatAsPWLHelper f state))

partial def formatEventGroup (vars : List Var) (inner : Formula) (state : FormatState) : String :=
  let indent := getIndentStr state
  let nextState := addIndent state
  s!"{indent}?[{varList_toString vars}]:(\n{formatAsPWLHelper inner nextState})"

end

def formatAsPWL (f : Formula) (boundVarOpt : Option Var) : String :=
  formatAsPWLHelper f ⟨0⟩

def serializeFormula (f : Formula) : String :=
  formatAsPWL f none

end PWL.Transform.Serialize

export PWL.Transform.Serialize (formatAsPWL serializeFormula)
