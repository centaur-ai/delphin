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
open Format
open PWL.Transform.Serialize (formatTheQ)

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

def defaultConfig : FormatConfig := { showImplicit := false }

instance : ToString (Bool × Nat × Option String) where
  toString v := toString v.1

partial def formatAsPWL (f : Formula) (lambdaVars : Lean.RBTree Var compare) 
    (bv : Option Var) (ind : Nat := 0) (inP : Bool := false) 
    (skipInitialIndent : Bool := false) (inNoQ : Bool := false) : String :=
  let indentStr := if skipInitialIndent then "" else makeIndent ind
  match f with
  | Formula.atom ep => 
    if ep.predicate == "implicit_conj" || ep.predicate == "_implicit_conj" ||
        ep.predicate == "and_c" || ep.predicate == "_and_c" then
      if ep.rargs.all (fun arg => arg.snd.sort == 'x') then 
        formatConjunction ep ind lambdaVars
      else
        formatPredArgs defaultConfig ep.predicate ep.rargs ep.carg ind inNoQ false
    else
      formatPredArgs defaultConfig ep.predicate ep.rargs ep.carg ind inNoQ false

  | Formula.scope vars (some "rstr_guard") inner =>
    let filteredVars := filterScopeVars defaultConfig vars
    if filteredVars.isEmpty then
      formatAsPWL inner lambdaVars bv ind inP skipInitialIndent inNoQ
    else 
      s!"{indentStr}?[{varList_toString filteredVars}]:(/* rstr_guard */\n{formatAsPWL inner lambdaVars bv (ind + 2) false false inNoQ})"

  | Formula.scope vars (some "body_guard") inner =>
    let filteredVars := filterScopeVars defaultConfig vars
    if filteredVars.isEmpty then
      formatAsPWL inner lambdaVars bv ind inP skipInitialIndent inNoQ
    else if inNoQ then
      match inner with
      | Formula.atom ep =>
        s!"{indentStr}?[{varList_toString filteredVars}]:(/* body_guard */\n{makeIndent (ind + 2)}~{formatPredArgs defaultConfig ep.predicate ep.rargs ep.carg (ind + 2) true true})"
      | _ =>
        s!"{indentStr}?[{varList_toString filteredVars}]:(/* body_guard */\n{makeIndent (ind + 2)}~({formatAsPWL inner lambdaVars bv (ind + 2) false true true}))"
    else
      s!"{indentStr}?[{varList_toString filteredVars}]:(/* body_guard */\n{formatAsPWL inner lambdaVars bv (ind + 2) false false inNoQ})"

  | Formula.scope vars (some q) inner => 
    let normalized := normalizePredicate q
    if (normalized == "neg" || normalized == "never_a_1") && vars.isEmpty then
      s!"{makeIndent ind}~{getNegComment normalized}{formatAsPWL inner lambdaVars bv ind false true true}"
    else
      match normalized with
      | "the_q" => formatTheQ vars inner ind (fun f bv ind inP skip => formatAsPWL f lambdaVars bv ind inP skip false)
      | "no_q" =>
        s!"{indentStr}~?[{varList_toString vars}]:(/* no_q */\n{formatAsPWL inner lambdaVars bv (ind + 2) false false false})"
      | "every_q" =>
        -- Handle universal quantifier differently
        match inner with
        | Formula.conj [rstr, body] =>
          -- Format as implication between restriction and body
          let rstrStr := formatAsPWL rstr lambdaVars bv (ind + 2) false false false
          let bodyStr := formatAsPWL body lambdaVars bv (ind + 2) false false false
          s!"{indentStr}![{varList_toString vars}]:(/* {normalized} */\n{rstrStr} =>\n{bodyStr})"
        | _ =>
          -- Fallback for other structures
          s!"{indentStr}![{varList_toString vars}]:(/* {normalized} */\n{formatAsPWL inner lambdaVars bv (ind + 2) false false false})"
      | _ =>
        let qtype := if normalized == "every_q" then "!" else "?"
        let filteredVars := filterScopeVars defaultConfig vars
        if filteredVars.isEmpty then
          formatAsPWL inner lambdaVars bv ind false false false
        else
          s!"{indentStr}{qtype}[{varList_toString filteredVars}]:(/* {normalized} */\n{formatAsPWL inner lambdaVars bv (ind + 2) false false false})"

  | Formula.scope vars none inner =>
    let filteredVars := filterScopeVars defaultConfig vars
    if filteredVars.isEmpty then
      formatAsPWL inner lambdaVars bv ind inP skipInitialIndent inNoQ
    else
      s!"{indentStr}?[{varList_toString filteredVars}]:(\n{formatAsPWL inner lambdaVars bv (ind + 2) false false inNoQ})"

  | Formula.conj [] => ""

  | Formula.conj [f] => 
    formatAsPWL f lambdaVars bv ind inP skipInitialIndent inNoQ

  | Formula.conj fs =>
    let nonEmpty := fs.filter (fun f => !f.isEmptyConj)
    String.intercalate " &\n" (nonEmpty.map (fun f => formatAsPWL f lambdaVars bv ind false false inNoQ))

end PWL.Transform

export PWL.Transform (formatAsPWL debugNested)
