import Mrs.Basic
import Mrs.PwlTypes
import Mrs.Hof
import Util.InsertionSort
import Lean.Data.RBTree

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

structure FormatConfig where
  showImplicit : Bool := false
  deriving Inhabited

def shouldShowVar (cfg : FormatConfig) (v : Var) : Bool :=
  if !cfg.showImplicit && v.sort == 'i' then
    false
  else true

def shouldShowScope (cfg : FormatConfig) (vars : List Var) : Bool :=
  vars.any (fun v => shouldShowVar cfg v)

def filterScopeVars (cfg : FormatConfig) (vars : List Var) : List Var :=
  if cfg.showImplicit then vars
  else vars.filter (shouldShowVar cfg)

def shouldShowArg (cfg : FormatConfig) (p : String × Var) : Bool :=
  shouldShowVar cfg p.2

def processAlways (args : List (String × Var)) : List (String × Var) :=
  let evars := args.filter (fun p => p.2.sort == 'e')
  let ivars := args.filter (fun p => p.2.sort == 'i')
  
  if evars.length == 1 && ivars.length == 1 then
    [evars.head!, ivars.head!]
  else
    args

def formatPredArgs (cfg : FormatConfig) (pred : String) (args : List (String × Var)) (carg : Option String) 
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
    let finalArgs := if pred == "always_a_1" || pred == "_always_a_1" then
                      processAlways args
                    else args
    
    let formatted := 
      if pred == "always_a_1" || pred == "_always_a_1" then
        match finalArgs with
        | [(_, e), (_, i)] => 
          if e.sort == 'e' && i.sort == 'i' then
            if cfg.showImplicit then
              s!"{pred}({e}) & arg1({e})={i}"
            else
              s!"{pred}({e})"
          else
            -- Fall back to standard formatting for non e/i pairs
            let argInfo := processArgs finalArgs
            let normalized := normalizePredicate pred
            match argInfo with
            | { firstArg := some firstArg, otherArgs := rest } =>
              let filtered := rest.filter (shouldShowArg cfg)
              let argStr := filtered.foldl (fun (acc : String × Nat) (p : String × Var) =>
                let argNum := acc.snd
                let str := if acc.fst.isEmpty
                  then s!"arg{argNum}({firstArg.2})={p.snd}"
                  else acc.fst ++ " & " ++ s!"arg{argNum}({firstArg.2})={p.snd}"
                (str, argNum + 1)
              ) ("", 1)
              if argStr.fst.isEmpty then
                s!"{normalized}({firstArg.2})"
              else
                s!"{normalized}({firstArg.2}) & {argStr.fst}"
            | _ => s!"{normalized}"
        | _ => s!"{pred}"
      else
        let argInfo := processArgs finalArgs
        let normalized := normalizePredicate pred
        dbg_trace s!"FORMAT_PRED: normalized={normalized} argInfo={argInfo} finalArgs={finalArgs}"
        match argInfo with
        | { firstArg := none, otherArgs := [] } => normalized
        | { firstArg := some firstArg, otherArgs := [] } => 
            s!"{normalized}({firstArg.2})"
        | { firstArg := none, otherArgs := rest } => s!"{normalized}({rest.head!.2})"
        | { firstArg := some firstArg, otherArgs := rest } =>
          let filtered := rest.filter (shouldShowArg cfg)
          let argStr := filtered.foldl (fun (acc : String × Nat) (p : String × Var) =>
            let argNum := acc.snd
            let str := if acc.fst.isEmpty
              then s!"arg{argNum}({firstArg.2})={p.snd}"
              else acc.fst ++ " & " ++ s!"arg{argNum}({firstArg.2})={p.snd}"
            (str, argNum + 1)
          ) ("", 1)
          if argStr.fst.isEmpty then
            s!"{normalized}({firstArg.2})"
          else
            s!"{normalized}({firstArg.2}) & {argStr.fst}"
    
    let needsParens := match pred with
    | "=" => false  
    | p => !p.endsWith "_q" && args.length > 1
    let result := if needsParens then s!"{indentStr}({formatted})" else s!"{indentStr}{formatted}"
    result

def getConjComment (pred : String) : String :=
  match pred with
  | "implicit_conj" | "_implicit_conj" => " /* implicit_conj */ "
  | "and_c" | "_and_c" => " /* and_c */ "
  | _ => ""

def formatConjunction (ep : EP) (indent : Nat) (lambdaVars : Lean.RBTree Var compare) : String :=
  dbg_trace s!"CONJ FORMAT: {ep.predicate} with args {ep.rargs.map (fun (n,v) => s!"{n}={v.sort}{v.id}")}"
  let baseIndent := makeIndent indent
  match ep.predicate with
  | "implicit_conj" | "_implicit_conj" | "and_c" | "_and_c" => 
    dbg_trace "-> matched conjunction"
    match ep.rargs with
    | [(_, x), (_, x1), (_, x2)] =>
      dbg_trace s!"-> found args ARG0={x.sort}{x.id} ARG1={x1.sort}{x1.id} ARG2={x2.sort}{x2.id}"
      if x.sort == 'x' && x1.sort == 'x' && x2.sort == 'x' then
        let ref1 := if lambdaVars.contains x1 then s!"{x1}(x)" else s!"x={x1}"
        let ref2 := if lambdaVars.contains x2 then s!"{x2}(x)" else s!"x={x2}"
        dbg_trace "-> all x-type args confirmed"
        s!"{baseIndent}{x}=^[x]:({getConjComment ep.predicate}\n{baseIndent}  {ref1} | {ref2})"
      else
        dbg_trace "-> using standard format (not all x-type)"
        s!"{baseIndent}({ep.predicate}({x}) & arg1({x})={x1} & arg2({x})={x2})"
    | _ => 
      dbg_trace "-> missing required args"
      s!"{baseIndent}{ep.predicate}"
  | _ => s!"{baseIndent}{ep.predicate}"

end PWL.Transform.Format

export PWL.Transform.Format (
  ArgInfo
  FormatConfig 
  processArgs
  varList_toString
  normalizePredicate 
  makeIndent
  formatPredArgs
  formatConjunction
  shouldShowScope
  filterScopeVars
)
