import Mrs.Basic
import Mrs.PwlTypes
import Mrs.Hof
import Mrs.PwlTransformShared
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
  toString a := s!"ArgInfo(first={a.firstArg}, rest={a.otherArgs})"

def debugNested (f : Formula) : String :=
  match f with
  | Formula.atom ep => s!"atom({ep.predicate})"
  | Formula.scope _ _ _ => "scope"
  | Formula.conj fs => s!"conj(len={fs.length})"

def getNegComment (q : String) : String :=
  match q with
  | "never_a_1" | "_never_a_1" => " /* never_a_1 */ "
  | "neg" | "_neg" => " /* neg */ "
  | _ => ""

def makeIndent (n : Nat) : String :=
  String.mk (List.replicate n ' ')

def formatWithGuardComments (rstrStr : String) (bodyStr : String) (qvar : Var) (ind : Nat) : String :=
  let indent := makeIndent (ind + 2)
  s!"{indent}/* RSTR[{qvar}] */\n{rstrStr} &\n{indent}/* BODY[{qvar}] */\n{bodyStr}"

instance : ToString (Bool × Nat × Option String) where
  toString v := toString v.1


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

structure FormatConfig where
  showImplicit : Bool := false
  deriving Inhabited

def defaultConfig : FormatConfig := { showImplicit := false }

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
  else if pred == "and_c" || pred == "_and_c" then
    dbg_trace s!"FORMAT_PRED: handling and_c with args={args}"
    match args with
    | ("ARG0", target) :: ("ARG1", v1) :: ("ARG2", v2) :: ("ARG3", v3) :: [] =>
      s!"{indentStr}(and_c({target}) & arg1({target})={v1} & arg2({target})={v2} & arg3({target})={v3})"
    | ("ARG0", target) :: ("ARG1", v1) :: ("ARG2", v2) :: [] =>
      s!"{indentStr}(and_c({target}) & arg1({target})={v1} & arg2({target})={v2})"
    | _ => s!"{indentStr}and_c"
  else 
    -- Rest of existing always/finalize handling
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
  let baseIndent := makeIndent indent
  match ep.predicate with 
  | "implicit_conj" | "_implicit_conj" | "and_c" | "_and_c" =>
    match ep.rargs with
    | [(_, x), (_, x1), (_, x2)] | [(_, x), (_, x1), (_, x2), (_, _)] =>  -- Match both 3 and 4 arg cases
      if x.sort == 'x' && x1.sort == 'x' && x2.sort == 'x' then
        let arg0 := ep.rargs.find? (fun p => p.1 == "ARG0") 
        let refs := ep.rargs.filter (fun p => p.1 != "ARG0" && p.2.sort == 'x') |>.map (·.2)
        match arg0 with
        | some (_, output) =>
          dbg_trace s!"CONJ_CHECK: {ep.predicate} output={output} lambdas={(lambdaVars.fold (init := []) fun xs x => x :: xs)}"
          -- Check if this lambda variable is referenced by other lambda definitions
          if lambdaVars.any (fun v => 
              -- Check if this lambda var references other lambda vars
              refs.any (fun r => lambdaVars.contains r) ||
              -- Is referenced by other lambda vars 
              v != output && lambdaVars.contains v) then
            let refStrings := refs.map (fun ref => s!"x={ref}")
            let disjunction := String.intercalate " | " refStrings  
            s!"{baseIndent}{output}=^[x]:({getConjComment ep.predicate}\n{baseIndent}  {disjunction})"
          else s!"{baseIndent}{ep.predicate}"
        | none => s!"{baseIndent}{ep.predicate}"
      else s!"{baseIndent}({ep.predicate}({x}) & arg1({x})={x1} & arg2({x})={x2})"
    | _ => s!"{baseIndent}{ep.predicate}"
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
  debugNested
  getNegComment
  formatWithGuardComments
)
