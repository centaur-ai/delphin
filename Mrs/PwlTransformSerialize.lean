import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping
import Mrs.PwlTransformMinScoping_Events
import Mrs.PwlTransformMinScoping_Core
import Mrs.PwlTransformFormat
import Mrs.PwlTransformSerializeTheQ
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform

open MRS (Var EP Constraint MRS)
open MM (Multimap)
open Lean (Format HashMap)
open InsertionSort
open HOF (lastTwoChars)
open PWL.Transform.MinScoping
open Format -- Using Format namespace for all formatting functions
open PWL.Transform.Serialize (formatTheQ) -- Only importing formatTheQ from Serialize

def debugNested (f : Formula) : String :=
  match f with
  | Formula.atom ep => s!"atom({ep.predicate})"
  | Formula.scope _ _ _ => "scope"
  | Formula.conj fs => s!"conj(len={fs.length})"

partial def formatAsPWL (f : Formula) (bv : Option Var) (ind : Nat := 0) (inP : Bool := false) (skipInitialIndent : Bool := false) : String :=
  let indentStr := if skipInitialIndent then "" else makeIndent ind

  match f with 
  | Formula.atom ep =>
    if (ep.predicate == "implicit_conj" || ep.predicate == "_implicit_conj" ||
        ep.predicate == "and_c" || ep.predicate == "_and_c") then
      if ep.rargs.all (fun arg => arg.2.sort == 'x') then
        formatConjunction ep ind
      else
        formatPredArgs ep.predicate ep.rargs ep.carg ind false
    else
      formatPredArgs ep.predicate ep.rargs ep.carg ind false

  | Formula.scope vars (some "rstr_guard") inner =>
    if vars.isEmpty then
      formatAsPWL inner bv ind inP skipInitialIndent
    else 
      s!"{indentStr}?[{varList_toString vars}]:(/* rstr_guard */\n{formatAsPWL inner bv (ind + 2) false false})"

  | Formula.scope vars (some "body_guard") inner =>
    if vars.isEmpty then
      formatAsPWL inner bv ind inP skipInitialIndent
    else
      s!"{indentStr}?[{varList_toString vars}]:(/* body_guard */\n{formatAsPWL inner bv (ind + 2) false false})"

  | Formula.scope vars (some q) inner => 
    let normalized := normalizePredicate q
    dbg_trace s!"Serializing scope with quantifier: {q} (normalized: {normalized})"
    if (normalized == "neg" || normalized == "never_a_1") && vars.isEmpty then
      s!"{indentStr}~{formatAsPWL inner bv ind false true}"  
    else
      match normalized with
      | "the_q" => formatTheQ vars inner ind (fun f bv ind inP skip => formatAsPWL f bv ind inP skip)
      | _ =>
        let qtype := if normalized == "every_q" then "!" else "?"
        s!"{indentStr}{qtype}[{varList_toString vars}]:(/* {normalized} */\n{formatAsPWL inner bv (ind + 2) false false})"

  | Formula.scope vars none inner =>
    if vars.isEmpty then
      formatAsPWL inner bv ind inP skipInitialIndent
    else
      s!"{indentStr}?[{varList_toString vars}]:(\n{formatAsPWL inner bv (ind + 2) false false})"

  | Formula.conj [] => ""

  | Formula.conj [f] => 
    formatAsPWL f bv ind inP skipInitialIndent

  | Formula.conj fs =>
    dbg_trace "CONJ START"
    let nonEmpty := fs.filter (fun f => !f.isEmptyConj)
    dbg_trace ("NONEMT: " ++ toString (nonEmpty.map debugNested))
    String.intercalate " &\n" (nonEmpty.map (fun f => formatAsPWL f bv ind false false))

end PWL.Transform

export PWL.Transform (formatAsPWL debugNested)
