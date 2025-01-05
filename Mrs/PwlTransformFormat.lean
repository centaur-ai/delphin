import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformMinScoping_Types
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

def processArgs (args : List (String × Var)) : ArgInfo :=
  dbg_trace s!"FORMAT.processArgs start\n  args: {args.map (fun p => (p.1, p.2))}"
  let ordered := args.filter (fun a => a.1.startsWith "ARG") |> insertionSort
  dbg_trace s!"FORMAT.processArgs ordered\n  filtered/sorted: {ordered.map (fun p => (p.1, p.2))}"
  match ordered with
  | [] => 
    dbg_trace "FORMAT.processArgs empty"
    ArgInfo.mk none []
  | first::rest => 
    dbg_trace s!"FORMAT.processArgs result\n  first: {first}\n  rest: {rest}"
    ArgInfo.mk (some first) rest

def varList_toString (vars : List Var) : String :=
  String.intercalate "," (vars.map toString)

def normalizePredicate (p : String) : String :=
  if p.startsWith "_" then p.drop 1 else p

def makeIndent (n : Nat) : String :=
  dbg_trace s!"FORMAT.makeIndent n={n}"
  String.mk (List.replicate n ' ')

def formatSinglePredicate (pred : String) (args : List (String × Var)) (indent : String) (carg : Option String) (isAtomWithRest : Bool := false) : String :=
  dbg_trace s!"FORMAT.formatSinglePredicate starting with:\n  pred={pred}\n  args={args}\n  indent='{indent}'\n  isAtomWithRest={isAtomWithRest}"
  
  -- Special case for equality predicate
  if pred == "=" then
    match args with
    | [(_, var1), (_, var2)] => 
      match carg with
      | some comment => s!"{indent}({var1} = {var2}) {comment}"
      | none => s!"{indent}({var1} = {var2})"
    | _ => indent ++ "=" -- fallback case though this shouldn't happen
  else
    -- Original formatting logic for other predicates
    let argInfo := processArgs args
    let normalized := normalizePredicate pred
    let formatted := match argInfo with
    | { firstArg := none, otherArgs := [] } =>
        normalized
    | { firstArg := some firstArg, otherArgs := [] } =>
        s!"{normalized}({firstArg.2})" 
    | { firstArg := none, otherArgs := rest } =>
        s!"{normalized}({rest.head!.2})"
    | { firstArg := some firstArg, otherArgs := rest } =>
        let argStr := rest.foldl (fun (acc : String × Nat) (pair : String × Var) =>
          let argNum := acc.2
          let str := if acc.1.isEmpty
            then s!"arg{argNum}({firstArg.2})={pair.2}"
            else acc.1 ++ " & " ++ s!"arg{argNum}({firstArg.2})={pair.2}"
          (str, argNum + 1)
        ) ("", 1)
        s!"({normalized}({firstArg.2}) & {argStr.1})"

    let needsParens := isAtomWithRest && !pred.endsWith "_q"
    let result := if needsParens then
      s!"{indent}({formatted})"
    else
      s!"{indent}{formatted}"
    
    dbg_trace s!"FORMAT.formatSinglePredicate returns: '{result}'"
    result

def formatPredArgs (pred : String) (args : List (String × Var)) (carg : Option String) (indent : Nat) (isAtomWithRest : Bool) : String :=
  let indentStr := makeIndent indent
  
  dbg_trace s!"FORMAT[{indent}]: pred={pred}, inParen={isAtomWithRest}, carg={carg}, args={args}"
  
  if pred == "named" || pred == "_named" then
    match args.find? (fun p => p.1 == "ARG0"), carg with
    | some (_, var), some str =>
      s!"{indentStr}?[n]:(name(n) & arg1(n)={var} & arg2(n)={str})"
    | _, _ =>
      s!"{indentStr}named({args.head!.2})"
  else
    formatSinglePredicate pred args indentStr carg isAtomWithRest

def formatConjunction (ep : EP) (indent : Nat) : String :=
  let indentStr := makeIndent indent
  let nextIndent := makeIndent (indent + 2)
  match ep.predicate with
  | "implicit_conj" | "_implicit_conj" | "and_c" | "_and_c" => 
    let arg0 := ep.rargs.find? (fun p => p.1 == "ARG0")
    let arg1 := ep.rargs.find? (fun p => p.1 == "ARG1")
    let arg2 := ep.rargs.find? (fun p => p.1 == "ARG2")
    match arg0, arg1, arg2 with 
    | some (_, x), some (_, x1), some (_, x2) =>
      if x.sort == 'x' && x1.sort == 'x' && x2.sort == 'x' then
        -- For x-type variables, output simpler format
        s!"{indentStr}{x}=^[x]:(\n{nextIndent}x={x1} | x={x2})"
      else
        s!"{indentStr}({ep.predicate}({x}) & arg1({x})={x1} & arg2({x})={x2})"
    | _, _, _ => s!"{indentStr}{ep.predicate}"
  | _ => s!"{indentStr}{ep.predicate}"

end PWL.Transform.Format

export PWL.Transform.Format (
  ArgInfo
  processArgs
  varList_toString
  normalizePredicate
  makeIndent
  formatSinglePredicate
  formatPredArgs
  formatConjunction
)
