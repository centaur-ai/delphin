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

def normalizePredicate (pred : String) : String :=
  if pred.startsWith "_" then pred.drop 1 else pred

def varList_toString (vars : List Var) : String :=
  String.intercalate "," (vars.map toString)

mutual 
-- Look for any scopable variable (x or e)
partial def findScopableVar : List (String × Var) → Option Var :=
  fun args => args.find? (fun p => p.snd.sort == 'x' || p.snd.sort == 'e') |>.map (fun p => p.snd)

partial def formatPredArgs (pred : String) (args : List (String × Var)) (carg : Option String) (indent : Nat) (isFirstInConj : Bool := false) : String :=
  let indentStr := if isFirstInConj then "" else String.mk (List.replicate (2 * indent) ' ')
  -- Special handling for named predicates first
  if pred == "named" || pred == "_named" then
    match args.find? (fun p => p.1 == "ARG0"), carg with
    | some (_, var), some str => 
      s!"{indentStr}?[n]:(name(n) & arg1(n)={var} & arg2(n)={str})"
    | _, _ => s!"{indentStr}named({args.head!.2})" -- fallback
  else
    -- Handle all other predicates with event variable ordering
    let orderedArgs := orderArgs args
    
    -- Find first event variable by ARG number
    let firstEvent := orderedArgs.find? (fun a => a.2.sort == 'e')

    match firstEvent, orderedArgs with
    | none, [] => indentStr ++ pred
    | none, (firstArg :: restArgs) =>
      -- No event variables - use original serialization
      let base := s!"{pred}({firstArg.2})"
      if restArgs.isEmpty then indentStr ++ base
      else
        let argStr := restArgs.foldl (fun (acc : String × Nat) (pair : String × Var) =>
          let argNum := acc.2
          let str := if acc.1.isEmpty 
            then s!"arg{argNum}({firstArg.2})={pair.2}"
            else acc.1 ++ " & " ++ s!"arg{argNum}({firstArg.2})={pair.2}"
          (str, argNum + 1)
        ) ("", 1)
        s!"{indentStr}({base} & {argStr.1})"
    | some eventArg, _ =>
      -- Found event variable - use it as base and adjust other args
      let otherArgs := orderedArgs.filter (fun a => a != eventArg)
      let base := s!"{pred}({eventArg.2})"
      if otherArgs.isEmpty then indentStr ++ base
      else
        let argStr := otherArgs.foldl (fun (acc : String × Nat) (pair : String × Var) =>
          let argNum := acc.2
          let str := if acc.1.isEmpty 
            then s!"arg{argNum}({eventArg.2})={pair.2}"
            else acc.1 ++ " & " ++ s!"arg{argNum}({eventArg.2})={pair.2}"
          (str, argNum + 1)
        ) ("", 1)
        s!"{indentStr}({base} & {argStr.1})"

partial def splitTheQParts (f : Formula) (boundVar : Var) : Option (Formula × Formula) :=
  match f with
  | Formula.atom ep =>
    dbg_trace s!"splitTheQParts examining atom: {ep}"
    match ep.rargs.find? (fun arg => arg.1 == "ARG0" && arg.2 == boundVar) with
    | some _ =>
      dbg_trace s!"Found restriction predicate for {boundVar}"
      some (Formula.atom ep, Formula.conj [])
    | none => 
      dbg_trace s!"No matching ARG0 found in atom"
      none
      
  | Formula.conj fs =>
    dbg_trace s!"splitTheQParts examining conjunction of {fs.length} formulas"
    match fs.find? (fun f => 
      match f with
      | Formula.atom ep => 
        ep.rargs.any (fun arg => arg.1 == "ARG0" && arg.2 == boundVar)
      | _ => false) with
    | some rstr =>
      dbg_trace s!"Found restriction in conjunction: {rstr}"
      let remainder := fs.filter (fun f => !BEq.beq f rstr)
      some (rstr, Formula.conj remainder)
    | none =>
      dbg_trace s!"No restriction found in conjunction formulas"
      none
      
  | _ => 
    dbg_trace "splitTheQParts: unhandled formula type"
    none

partial def formatTheQ (vars : List Var) (inner : Formula) (indent : Nat) : String :=
  match vars with
  | [] => "ERROR: no variables for the_q"
  | boundVar :: _ =>
    match splitTheQParts inner boundVar with 
    | some (rstr, body) =>
      dbg_trace s!"Formatting the_q with restriction: {rstr}"
      s!"?[S]:(/* the_q */ S=^[s]:{formatAsPWL rstr none indent} & size(S)=1 & S({boundVar}) &\n{formatAsPWL body none (indent + 1)})"
    | none =>
      dbg_trace "No restriction found for the_q, using default format"  
      s!"?[{varList_toString vars}]:(/* the_q */\n{formatAsPWL inner none (indent + 1)})"

partial def formatScopedPredicate (vars : List Var) (pred : String) (inner : Formula) (indent : Nat) : String :=
  let var := match vars with
  | [] => "ERROR_NO_VAR"
  | v :: _ => toString v
  if pred == "colon_p_namely" || pred == "_colon_p_namely" then
    match inner with
    | Formula.conj [f1, f2] =>
      s!"(\n{formatAsPWL f1 none (indent + 1)} &\n{formatAsPWL f2 none (indent + 1)})"
    | _ => s!"(\n{formatAsPWL inner none (indent + 1)})"
  else  -- neg case
    s!"~(/* {pred}({var}) */\n{formatAsPWL inner none (indent + 1)})"

partial def formatAsPWL (f : Formula) (boundVarOpt : Option Var) (indent : Nat := 0) : String :=
  let indentStr := String.mk (List.replicate (2 * indent) ' ')
  match f, boundVarOpt with 
  | Formula.scope vars (some q) inner, _ => 
    dbg_trace s!"formatAsPWL examining quant: {q}"
    let normalizedQuant := normalizePredicate q
    match normalizedQuant with
    | "the_q" =>
      dbg_trace "formatAsPWL processing the_q"
      indentStr ++ formatTheQ vars inner (indent + 1)
    | "every_q" =>
      dbg_trace "formatAsPWL processing every_q"  
      indentStr ++ s!"![{varList_toString vars}]:(/* every_q */\n{formatAsPWL inner none (indent + 1)})"
    | "never_a_1" | "neg" | "colon_p_namely" =>
      dbg_trace s!"formatAsPWL processing scoped predicate: {normalizedQuant}"
      indentStr ++ formatScopedPredicate vars normalizedQuant inner indent
    | _ =>
      dbg_trace s!"formatAsPWL processing other quant: {normalizedQuant}"
      indentStr ++ s!"?[{varList_toString vars}]:(/* {normalizedQuant} */\n{formatAsPWL inner none (indent + 1)})"

  | Formula.scope vars none inner, _ => 
    dbg_trace "formatAsPWL processing non-quant scope"
    indentStr ++ s!"?[{varList_toString vars}]:(\n{formatAsPWL inner none (indent + 1)})"

  | Formula.atom ep, _ => 
    dbg_trace s!"formatAsPWL processing atom: {ep}"
    formatPredArgs ep.predicate ep.rargs ep.carg indent false

  | Formula.conj [], _ => ""
  | Formula.conj [f], boundVar => formatAsPWL f boundVar indent
  | Formula.conj fs, boundVar =>
    dbg_trace s!"formatAsPWL processing conjunction size: {fs.length}"
    let nonEmpty := fs.filter (fun f => !f.isEmptyConj)
    match nonEmpty with
    | [] => ""
    | [Formula.atom ep, rest] => 
      if normalizePredicate ep.predicate |>.endsWith "_q" then
        dbg_trace s!"formatAsPWL found quantifier: {ep.predicate}"
        indentStr ++ s!"({formatPredArgs ep.predicate ep.rargs ep.carg indent true}\n{formatAsPWL (Formula.conj [rest]) boundVar indent})"
      else
        dbg_trace s!"formatAsPWL found non-quantifier: {ep.predicate}"
        let restStr := formatAsPWL (Formula.conj [rest]) boundVar indent
        if restStr.isEmpty then
          formatPredArgs ep.predicate ep.rargs ep.carg indent false
        else
          indentStr ++ s!"({formatPredArgs ep.predicate ep.rargs ep.carg indent true} &\n{restStr})"
    | fs => 
      indentStr ++ "(" ++ (fs.foldl (fun (acc : String × Bool) f =>
        match f with
        | Formula.atom ep =>
          let fStr := if acc.2 
            then formatPredArgs ep.predicate ep.rargs ep.carg indent true
            else formatPredArgs ep.predicate ep.rargs ep.carg indent false
          (acc.1 ++ (if acc.1.isEmpty then fStr else " &\n" ++ fStr), false)
        | _ => acc) ("", true)).1 ++ ")"

end

end PWL.Transform.Serialize

export PWL.Transform.Serialize (formatAsPWL)
