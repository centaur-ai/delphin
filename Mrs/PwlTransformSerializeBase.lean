import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.Serialize

open MRS (Var EP)
open Lean (Format)
open HOF (lastTwoChars)
open InsertionSort

structure ArgInfo where
  firstArg : Option (String × Var)
  otherArgs : List (String × Var)
  deriving Inhabited

def processArgs (args : List (String × Var)) : ArgInfo :=
  dbg_trace s!"BASE.processArgs start\n  args: {args.map (fun p => (p.1, p.2))}"
  let ordered := args.filter (fun a => a.1.startsWith "ARG") |> insertionSort
  dbg_trace s!"BASE.processArgs ordered\n  filtered/sorted: {ordered.map (fun p => (p.1, p.2))}"
  match ordered with
  | [] => 
    dbg_trace "BASE.processArgs empty"
    { firstArg := none, otherArgs := [] }
  | first::rest => 
    dbg_trace s!"BASE.processArgs result\n  first: {first}\n  rest: {rest}"
    { firstArg := some first, otherArgs := rest }

def varList_toString (vars : List Var) : String :=
  String.intercalate "," (vars.map toString)

def normalizePredicate (p : String) : String :=
  if p.startsWith "_" then p.drop 1 else p

def makeIndent (n : Nat) : String :=
  dbg_trace s!"BASE.makeIndent n={n}"
  String.mk (List.replicate n ' ')

def formatSinglePredicate (pred : String) (args : List (String × Var)) (indent : String) (isAtomWithRest : Bool := false) : String :=
  dbg_trace s!"BASE.formatSinglePredicate starting with:\n  pred={pred}\n  args={args}\n  indent='{indent}'\n  isAtomWithRest={isAtomWithRest}"
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
  
  -- Only add outer parentheses if it's an atom with rest and not a quantifier
  let needsParens := isAtomWithRest && !pred.endsWith "_q"
  let result := if needsParens then
    s!"{indent}({formatted})"
  else
    s!"{indent}{formatted}"
    
  dbg_trace s!"BASE.formatSinglePredicate returns: '{result}'"
  result

def formatPredArgs (pred : String) (args : List (String × Var)) (carg : Option String)
                  (indent : Nat) (isAtomWithRest : Bool := false) : String :=
  let indentStr := makeIndent indent
  
  dbg_trace s!"PREDARG[{indent}]: pred={pred}, inParen={isAtomWithRest}, carg={carg}, args={args}"
  
  if pred == "named" || pred == "_named" then
    match args.find? (fun p => p.1 == "ARG0"), carg with
    | some (_, var), some str =>
      s!"{indentStr}(name(n) & arg1(n)={var} & arg2(n)={str})"
    | _, _ =>
      s!"{indentStr}named({args.head!.2})"
  else 
    formatSinglePredicate pred args indentStr isAtomWithRest

end PWL.Transform.Serialize

export PWL.Transform.Serialize (ArgInfo processArgs varList_toString normalizePredicate makeIndent formatSinglePredicate formatPredArgs)
