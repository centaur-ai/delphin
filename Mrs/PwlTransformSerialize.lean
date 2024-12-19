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
partial def findFirstXVar : List (String × Var) → Option Var :=
  fun args => args.find? (fun p => p.snd.sort == 'x') |>.map (fun p => p.snd)

partial def formatPredArgs (pred : String) (args : List (String × Var)) (carg : Option String) : String :=
  match findFirstXVar args with
  | some xvar => 
    dbg_trace s!"formatPredArgs found x-var: {xvar}"
    let base := s!"{normalizePredicate pred}"
    if pred == "named" || pred == "_named" then
      match carg with
      | some c => 
        s!"({base}({xvar}) & arg1({xvar})=\"{removeQuotes c}\")"
      | none => s!"{base}({xvar})"
    else
      let nonXArgs := args.filter (fun p => p.2.sort ≠ 'x')
      if nonXArgs.isEmpty then
        s!"{base}({xvar})"
      else
        let argStr := nonXArgs.foldl (fun (acc : String × Nat) (pair : String × Var) =>
          let argNum := acc.2
          let str := if acc.1.isEmpty 
            then s!"arg{argNum}({xvar})={pair.2}"
            else acc.1 ++ " & " ++ s!"arg{argNum}({xvar})={pair.2}"
          (str, argNum + 1)
        ) ("", 1)
        s!"({base}({xvar}) & {argStr.1})"
  | none =>
    match args with 
    | [] => 
      dbg_trace s!"formatPredArgs no args for: {pred}"
      normalizePredicate pred
    | (_, first) :: rest =>
      dbg_trace s!"formatPredArgs using first arg: {first}"
      let base := s!"{normalizePredicate pred}({first})"
      if rest.isEmpty then 
        dbg_trace s!"formatPredArgs using base only: {base}"
        base
      else 
        let argStr := rest.foldl (fun (acc : String × Nat) (pair : String × Var) =>
          let argNum := acc.2
          let str := if acc.1.isEmpty 
            then s!"arg{argNum}({first})={pair.2}"
            else acc.1 ++ " & " ++ s!"arg{argNum}({first})={pair.2}"
          (str, argNum + 1)
        ) ("", 1)
        s!"({base} & {argStr.1})"

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

partial def formatTheQ (vars : List Var) (inner : Formula) : String :=
  match vars with
  | [] => "ERROR: no variables for the_q"
  | boundVar :: _ =>
    match splitTheQParts inner boundVar with 
    | some (rstr, body) =>
      dbg_trace s!"Formatting the_q with restriction: {rstr}"
      s!"?[S]:(/* the_q */ S=^[s]:{formatAsPWL rstr none} & size(S)=1 & S({boundVar}) & {formatAsPWL body none})"
    | none =>
      dbg_trace "No restriction found for the_q, using default format"  
      s!"?[{varList_toString vars}]:(/* the_q */ {formatAsPWL inner none})"

partial def formatAsPWL (f : Formula) (boundVarOpt : Option Var) : String :=
  match f, boundVarOpt with 
  | Formula.scope vars (some q) inner, _ => 
    dbg_trace s!"formatAsPWL scope with vars: {vars}"
    let normalizedQuant := normalizePredicate q
    dbg_trace s!"formatAsPWL examining quant: {normalizedQuant}"
    if normalizedQuant == "the_q" then
      dbg_trace "formatAsPWL processing the_q"
      formatTheQ vars inner
    else if normalizedQuant == "every_q" then
      dbg_trace "formatAsPWL processing every_q"  
      s!"![{varList_toString vars}]:(/* every_q */ {formatAsPWL inner none})"
    else
      dbg_trace s!"formatAsPWL processing other quant: {normalizedQuant}"
      s!"?[{varList_toString vars}]:(/* {normalizedQuant} */ {formatAsPWL inner none})"

  | Formula.neg nt inner, _ =>
    dbg_trace "formatAsPWL processing negation"
    let negStr := match nt with
      | NegationType.Never i => s!"never_a_1({i})"
      | NegationType.NegWithEvent e => s!"neg({e})"
    s!"~(/* {negStr} */ {formatAsPWL inner none})"

  | Formula.scope vars none inner, _ => 
    dbg_trace "formatAsPWL processing non-quant scope"
    s!"?[{varList_toString vars}]:({formatAsPWL inner none})"

  | Formula.atom ep, _ => 
    dbg_trace s!"formatAsPWL processing atom: {ep}"
    formatPredArgs ep.predicate ep.rargs ep.carg

  | Formula.conj [], _ => ""
  | Formula.conj [f], boundVar => formatAsPWL f boundVar
  | Formula.conj fs, boundVar =>
    dbg_trace s!"formatAsPWL processing conjunction size: {fs.length}"
    let nonEmpty := fs.filter (fun f => !f.isEmptyConj)
    match nonEmpty with
    | [] => ""
    | [Formula.atom ep, rest] => 
      if normalizePredicate ep.predicate |>.endsWith "_q" then
        dbg_trace s!"formatAsPWL found quantifier: {ep.predicate}"
        s!"({formatAsPWL (Formula.atom ep) boundVar} {formatAsPWL (Formula.conj [rest]) boundVar})"
      else
        dbg_trace s!"formatAsPWL found non-quantifier: {ep.predicate}"
        s!"({formatAsPWL (Formula.atom ep) boundVar} & {formatAsPWL (Formula.conj [rest]) boundVar})"
    | fs => s!"({String.intercalate " & " (fs.map (fun f => formatAsPWL f boundVar))})"
end

partial def substituteVar (oldVar newVar : Var) (f : Formula) : String :=
  match f with
  | Formula.atom ep =>
    dbg_trace s!"substituteVar atom old: {oldVar} new: {newVar}"
    let args := ep.rargs.map fun (s, v) => (s, if v == oldVar then newVar else v)
    let args' := if args.any (fun (_, v) => v == newVar)
      then args else args
    formatPredArgs ep.predicate args' ep.carg

  | Formula.conj [] => ""
  | Formula.conj [f] => substituteVar oldVar newVar f
  | Formula.conj fs => s!"({String.intercalate " & " (fs.map (substituteVar oldVar newVar))})"

  | Formula.neg nt inner =>
    dbg_trace s!"substituteVar negation old: {oldVar} new: {newVar}"
    match nt with
    | NegationType.Never i => s!"~(/* never_a_1({i}) */ {substituteVar oldVar newVar inner})"
    | NegationType.NegWithEvent e => s!"~(/* neg({e}) */ {substituteVar oldVar newVar inner})"

  | Formula.scope vars quant inner =>
    dbg_trace s!"substituteVar scope vars: {vars}"
    if vars.any (· == oldVar) then
      dbg_trace "substituteVar skipping due to bound var"
      formatAsPWL (Formula.scope vars quant inner) none
    else 
      match quant with
      | none => s!"?[{varList_toString vars}]:({substituteVar oldVar newVar inner})"
      | some "every_q" => s!"![{varList_toString vars}]:(/* every_q */ {substituteVar oldVar newVar inner})"
      | some q => s!"?[{varList_toString vars}]:(/* {normalizePredicate q} */ {substituteVar oldVar newVar inner})"

end PWL.Transform.Serialize

export PWL.Transform.Serialize (formatAsPWL)
