import Mrs.Basic
import Mrs.PwlTypes
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.Format 

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

structure ArgInfo where
  firstArg : Option (String × Var)
  otherArgs : List (String × Var)
  deriving Inhabited

instance : ToString ArgInfo where
  toString
    | ⟨first, rest⟩ => s!"ArgInfo(first={first}, rest={rest})"

def processArgs (args : List (String × Var)) : ArgInfo :=
  dbg_trace s!"ARGS analysis: input={args.map fun a => (a.1, a.2)}"
  let ordered := args.filter (fun a => a.1.startsWith "ARG") |> insertionSort
  let result := (match ordered with
  | [] => { firstArg := none, otherArgs := [] }
  | first::rest => { firstArg := some first, otherArgs := rest })
  result

def varList_toString (vars : List Var) : String :=
  String.intercalate "," (vars.map toString)

def normalizePredicate (p : String) : String :=
  if p.startsWith "_" then p.drop 1 else p

def makeIndent (n : Nat) : String :=
  String.mk (List.replicate n ' ')

def formatSinglePredicate (pred : String) (args : List (String × Var)) (indent : String) 
    (carg : Option String) (isAtomWithRest : Bool := false) : String :=
  dbg_trace s!"FORMAT_SINGLE: pred={pred} args={args} carg={carg} isAtomWithRest={isAtomWithRest}"
  (if pred == "=" then
    (match args with
    | [(_, var1), (_, var2)] => 
      (match carg with
      | some comment => s!"{indent}({var1} = {var2}) {comment}"
      | none => s!"{indent}({var1} = {var2})")
    | _ => indent ++ "=")
  else
    let argInfo := processArgs args
    let normalized := normalizePredicate pred
    let formatted := (match argInfo with
    | { firstArg := none, otherArgs := [] } => normalized
    | { firstArg := some firstArg, otherArgs := [] } => 
        dbg_trace s!"FORMAT_SINGLE: single arg case first={firstArg}"
        s!"{normalized}({firstArg.2})"
    | { firstArg := none, otherArgs := rest } => s!"{normalized}({rest.head!.2})"
    | { firstArg := some firstArg, otherArgs := rest } =>
      dbg_trace s!"FORMAT_SINGLE: multi-arg case first={firstArg} rest={rest}"
      let argStr := rest.foldl (fun (acc : String × Nat) (pair : String × Var) =>
        let argNum := acc.2
        let str := if acc.1.isEmpty
          then s!"arg{argNum}({firstArg.2})={pair.2}"
          else acc.1 ++ " & " ++ s!"arg{argNum}({firstArg.2})={pair.2}"
        (str, argNum + 1)
      ) ("", 1)
      s!"({normalized}({firstArg.2}) & {argStr.1})")
    
    dbg_trace s!"FORMAT_SINGLE: pre-paren formatted='{formatted}'"
    let needsParens := isAtomWithRest && !pred.endsWith "_q"
    let result := if needsParens then s!"{indent}({formatted})" else s!"{indent}{formatted}"
    dbg_trace s!"FORMAT_SINGLE: final result='{result}'"
    result)

def formatPredArgs (pred : String) (args : List (String × Var)) (carg : Option String) 
    (indent : Nat) (inNegation : Bool) (skipInitialIndent : Bool := false) : String :=
  dbg_trace s!"FORMAT_PRED: start pred={pred} args={args} inNegation={inNegation}"
  let indentStr := if skipInitialIndent then "" else makeIndent indent
  
  if pred == "_named" || pred == "named" then
    match args.head?, carg with
    | some (_, var), some str => 
      s!"{indentStr}?[n]:(name(n) & arg1(n)={var} & arg2(n)={str})"
    | _, _ => unreachable!
  else if pred == "=" then
    match args with
    | [(_, var1), (_, var2)] => 
      match carg with
      | some comment => s!"{indentStr}({var1} = {var2}) {comment}"
      | none => s!"{indentStr}({var1} = {var2})"
    | _ => s!"{indentStr}="
  else 
    let argInfo := processArgs args
    let normalized := normalizePredicate pred
    dbg_trace s!"FORMAT_PRED: normalized={normalized} argInfo={argInfo}"
    let formatted := (match argInfo with
    | { firstArg := none, otherArgs := [] } => normalized
    | { firstArg := some firstArg, otherArgs := [] } => 
        dbg_trace s!"FORMAT_PRED: single arg case first={firstArg}"
        s!"{normalized}({firstArg.2})"
    | { firstArg := none, otherArgs := rest } => s!"{normalized}({rest.head!.2})"
    | { firstArg := some firstArg, otherArgs := rest } =>
      dbg_trace s!"FORMAT_PRED: multi-arg case first={firstArg} rest={rest}"
      let argStr := rest.foldl (fun (acc : String × Nat) (pair : String × Var) =>
        let argNum := acc.2
        let str := if acc.1.isEmpty
          then s!"arg{argNum}({firstArg.2})={pair.2}"
          else acc.1 ++ " & " ++ s!"arg{argNum}({firstArg.2})={pair.2}"
        (str, argNum + 1)
      ) ("", 1)
      s!"{normalized}({firstArg.2}) & {argStr.1}")
    
    dbg_trace s!"FORMAT_PRED: pre-indent formatted='{formatted}'"
    let needsParens := !inNegation && !pred.endsWith "_q"
    let result := if needsParens then s!"{indentStr}({formatted})" else s!"{indentStr}{formatted}"
    dbg_trace s!"FORMAT_PRED: final result='{result}'"
    result

def formatConjunction (ep : EP) (indent : Nat) : String :=
  dbg_trace s!"FORMAT_CONJ: predicate={ep.predicate} args={ep.rargs}"
  let indentStr := makeIndent indent
  (match ep.predicate with
  | "implicit_conj" | "_implicit_conj" | "and_c" | "_and_c" => 
    dbg_trace "FORMAT_CONJ: handling conjunction case"
    let arg0 := ep.rargs.find? (fun p => p.1 == "ARG0")
    let arg1 := ep.rargs.find? (fun p => p.1 == "ARG1") 
    let arg2 := ep.rargs.find? (fun p => p.1 == "ARG2")
    dbg_trace s!"FORMAT_CONJ: found args ARG0={arg0} ARG1={arg1} ARG2={arg2}"
    (match arg0, arg1, arg2 with
    | some (_, x), some (_, x1), some (_, x2) =>
      if x.sort == 'x' && x1.sort == 'x' && x2.sort == 'x' then
        let result := s!"{indentStr}{x}=^[x]:(\n{makeIndent (indent + 2)}x={x1} | x={x2})"
        dbg_trace s!"FORMAT_CONJ: x-vars result='{result}'"
        result
      else
        let result := s!"{indentStr}({ep.predicate}({x}) & arg1({x})={x1} & arg2({x})={x2})"
        dbg_trace s!"FORMAT_CONJ: mixed vars result='{result}'"
        result
    | _, _, _ => 
      dbg_trace "FORMAT_CONJ: missing args, using base predicate"
      s!"{indentStr}{ep.predicate}")
  | _ => 
    dbg_trace "FORMAT_CONJ: non-conjunction predicate"
    s!"{indentStr}{ep.predicate}")

end PWL.Transform.Format

export PWL.Transform.Format (
  ArgInfo
  processArgs
  varList_toString
  normalizePredicate 
  makeIndent
  formatSinglePredicate
  formatPredArgs
  formatConjunction)
