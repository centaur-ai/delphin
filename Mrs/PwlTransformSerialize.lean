import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformScoping
import Mrs.PwlTransformMinScoping
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform

open MRS (Var EP Constraint MRS)
open MM (Multimap)
open Lean (Format HashMap)
open InsertionSort
open HOF (lastTwoChars)
open PWL.Transform

structure ArgInfo where
  firstArg : Option (String × Var)
  otherArgs : List (String × Var)
  deriving Inhabited

def normalizePredicate (p : String) : String :=
  if p.startsWith "_" then p.drop 1 else p

def varList_toString (vars : List Var) : String :=
  String.intercalate "," (vars.map toString)

mutual 
  partial def formatAsPWL (f : Formula) (bv : Option Var) (ind : Nat := 0) (inP : Bool := false) (skipInitialIndent : Bool := false) : String :=
    let indentStr := String.mk (List.replicate ind ' ')
    let effectiveIndentStr := if skipInitialIndent then "" else indentStr
    match f with 
    | Formula.scope vars (some q) inner => 
      let normalizedQuant := normalizePredicate q
      match normalizedQuant with
      | "the_q" => formatTheQ vars inner ind
      | "every_q" =>
        s!"{effectiveIndentStr}![{varList_toString vars}]:(/* every_q */\n{formatAsPWL inner bv (ind + 2) false false}"
      | "never_a_1" | "neg" =>
        s!"{effectiveIndentStr}?[{varList_toString vars}]:(/* {normalizedQuant} */\n" ++
        s!"{indentStr}  ~{formatAsPWL inner bv (ind + 2) false true}"
      | _ =>
        s!"{effectiveIndentStr}?[{varList_toString vars}]:(/* {normalizedQuant} */\n{formatAsPWL inner bv (ind + 2) false false}"
    | Formula.scope vars none inner =>
      s!"{effectiveIndentStr}?[{varList_toString vars}]:(\n{formatAsPWL inner bv (ind + 2) false false}"
    | Formula.atom ep =>
      formatPredArgs ep.predicate ep.rargs ep.carg (if skipInitialIndent then 0 else ind) inP
    | Formula.conj [] => ""
    | Formula.conj [f] => formatAsPWL f bv ind inP skipInitialIndent
    | Formula.conj fs =>
      let nonEmpty := fs.filter (fun f => !f.isEmptyConj)
      match nonEmpty with
      | [] => ""
      | [Formula.atom ep, rest] =>
        if lastTwoChars ep.predicate |>.endsWith "_q" then
          s!"{effectiveIndentStr}({formatPredArgs ep.predicate ep.rargs ep.carg ind true}\n{formatAsPWL (Formula.conj [rest]) bv ind false false})"
        else
          let restStr := formatAsPWL (Formula.conj [rest]) bv ind false false
          if restStr.isEmpty then
            formatPredArgs ep.predicate ep.rargs ep.carg (if skipInitialIndent then 0 else ind) true
          else
            s!"{formatPredArgs ep.predicate ep.rargs ep.carg (if skipInitialIndent then 0 else ind) true} &\n{restStr}"
      | fs =>
        let formatGroup (f : Formula) : String :=
          match f with
          | Formula.atom ep =>
            let hasArgs := ep.rargs.length > 1 || ep.rargs.any (fun arg => arg.1.startsWith "arg")
            formatPredArgs ep.predicate ep.rargs ep.carg (if skipInitialIndent then 0 else ind) hasArgs
          | _ => formatAsPWL f bv (ind + 2) false false
        String.intercalate " &\n" (fs.map formatGroup)

  partial def formatTheQ (vars : List Var) (inner : Formula) (ind : Nat) : String :=
    let baseIndent := String.mk (List.replicate ind ' ')
    let contentIndent := String.mk (List.replicate (ind + 2) ' ')
    let innerIndent := String.mk (List.replicate (ind + 4) ' ')
    match vars.head? with
    | none => unreachable!
    | some x =>
      let innerFormatted := formatAsPWL inner none (ind + 4) false false
      s!"{baseIndent}?[S]:(/* the_q */\n{contentIndent}S=^[s]:\n{innerIndent}size(S)=1 & S({x}) &\n{innerFormatted}"

  partial def formatConjunction (ep : EP) (ind : Nat) : String :=
    let baseIndent := String.mk (List.replicate ind ' ')
    match ep.predicate with
    | "implicit_conj" | "_implicit_conj" | "and_c" | "_and_c" => 
      -- Extract ARG1 and ARG2
      let arg0 := ep.rargs.find? (fun p => p.1 == "ARG0")
      let arg1 := ep.rargs.find? (fun p => p.1 == "ARG1")
      let arg2 := ep.rargs.find? (fun p => p.1 == "ARG2")
      match arg0, arg1, arg2 with 
      | some (_, x), some (_, x1), some (_, x2) =>
        if x.sort == 'x' && x1.sort == 'x' && x2.sort == 'x' then
          s!"{baseIndent}?[S]:(\n{baseIndent}  S=^[x]:\n{baseIndent}    (x={x1} | x={x2}))"
        else
          s!"{baseIndent}({ep.predicate}({x}) & arg1({x})={x1} & arg2({x})={x2})"
      | _, _, _ => s!"{baseIndent}{ep.predicate}"
    | _ => s!"{baseIndent}{ep.predicate}"

  partial def processArgs (args : List (String × Var)) : ArgInfo :=
    let ordered := args.filter (fun a => a.1.startsWith "ARG") |> insertionSort
    match ordered with
    | [] => { firstArg := none, otherArgs := [] }
    | first::rest => { firstArg := some first, otherArgs := rest }

  partial def formatPredArgs (pred : String) (args : List (String × Var)) (carg : Option String)
                            (indent : Nat) (inParen : Bool) : String :=
    let indentStr := String.mk (List.replicate indent ' ')
    if pred == "named" || pred == "_named" then
      match args.find? (fun p => p.1 == "ARG0"), carg with
      | some (_, var), some str =>
        s!"{indentStr}name(n) & arg1(n)={var} & arg2(n)={str}"
      | _, _ =>
        s!"{indentStr}named({args.head!.2})"
    else 
      let normalizedPred := normalizePredicate pred
      if (normalizedPred == "implicit_conj" || normalizedPred == "and_c") && args.all (fun arg => arg.2.sort == 'x') then
        -- Get the arguments
        let arg0 := args.find? (fun arg => arg.1 == "ARG0")
        let arg1 := args.find? (fun arg => arg.1 == "ARG1")
        let arg2 := args.find? (fun arg => arg.1 == "ARG2") 
        match arg0, arg1, arg2 with
        | some (_, v0), some (_, v1), some (_, v2) =>
          s!"{indentStr}?[S]:(/* {normalizedPred} */\n{indentStr}  S=^[{v0}]:\n{indentStr}    ({v0}={v1} | {v0}={v2}))"
        | _, _, _ => formatNormalPredArgs pred args carg indent inParen
      else
        formatNormalPredArgs pred args carg indent inParen

  partial def formatNormalPredArgs (pred : String) (args : List (String × Var)) (carg : Option String)
                            (indent : Nat) (inParen : Bool) : String :=
    let indentStr := String.mk (List.replicate indent ' ')
    let argInfo := processArgs args
    match argInfo with
    | { firstArg := none, otherArgs := [] } =>
      indentStr ++ normalizePredicate pred
    | { firstArg := some firstArg, otherArgs := [] } =>
      s!"{indentStr}{normalizePredicate pred}({firstArg.2})"
    | { firstArg := some firstArg, otherArgs := rest } =>
      let argStr := rest.foldl (fun (acc : String × Nat) (pair : String × Var) =>
        let argNum := acc.2
        let str := if acc.1.isEmpty
          then s!"arg{argNum}({firstArg.2})={pair.2}"
          else acc.1 ++ " & " ++ s!"arg{argNum}({firstArg.2})={pair.2}"
        (str, argNum + 1)
      ) ("", 1)
      s!"{indentStr}({normalizePredicate pred}({firstArg.2}) & {argStr.1})"
    | { firstArg := none, otherArgs := rest } =>
      s!"{indentStr}{normalizePredicate pred}({rest.head!.2})"

end

end PWL.Transform

export PWL.Transform (formatAsPWL)
