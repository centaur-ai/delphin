import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS
open InsertionSort
open PWL.Transform
open Lean (HashMap)
open BEq

def getRequiredVarsForPredicate (ep : EP) : List Var :=
  let required := ep.rargs.map (fun x => x.2) |>.filter (fun v => v.sort == 'x' || v.sort == 'e')
  dbg_trace s!"Required vars for {ep.predicate}: {required.map (fun v => s!"{v.sort}{v.id}")}"
  required

partial def getPredicatesFromFormula (f : Formula) (level : Nat) : List EP :=
  (match f with
  | Formula.atom ep => 
    dbg_trace s!"[Level {level}] Found predicate: {ep.predicate}
      Args: {ep.rargs.map (fun x => s!"{x.1}={x.2.sort}{x.2.id}")}
      Label: h{ep.label.id}"
    [ep]
  | Formula.conj fs => 
    dbg_trace s!"[Level {level}] Processing conjunction of {fs.length} formulas"
    fs.foldl (fun acc f => acc ++ getPredicatesFromFormula f (level + 1)) []
  | Formula.scope vars quant inner => 
    dbg_trace s!"[Level {level}] Found scope
      Vars: {vars.map (fun v => s!"{v.sort}{v.id}")}
      Quant: {quant}"
    getPredicatesFromFormula inner (level + 1))

partial def getFormulaScopes (f : Formula) (level : Nat) : List ScopeInfo :=
  (match f with 
  | Formula.atom _ => []
  | Formula.conj fs => 
    dbg_trace s!"[Level {level}] Analyzing scope structure of conjunction"
    fs.foldl (fun acc f => acc ++ getFormulaScopes f (level + 1)) []
  | Formula.scope vars (some pred) inner => 
    dbg_trace s!"[Level {level}] Found scoped quantifier
      Predicate: {pred}
      Bound vars: {vars.map (fun v => s!"{v.sort}{v.id}")}"
    let normalized := if pred.startsWith "_" then pred.drop 1 else pred
    let scopeType := 
      if normalized == "every_q" then ScopeType.Universal 
      else if normalized == "the_q" || normalized == "def_explicit_q" then ScopeType.Definite
      else if normalized == "never_a_1" then ScopeType.NeverNeg
      else if normalized == "neg" then ScopeType.RegNeg
      else if normalized == "colon_p_namely" then ScopeType.ColonNamely
      else ScopeType.Indefinite
    let info : ScopeInfo := {
      predicate := normalized,
      boundVars := orderVarsForScoping vars.eraseDups,
      scopeType := scopeType,
      negVar := if vars.isEmpty then none else some vars.head! }
    dbg_trace s!"[Level {level}] Created scope info:
      Type: {toString scopeType}
      Available vars: {vars.map (fun v => s!"{v.sort}{v.id}")}"
    info :: getFormulaScopes inner (level + 1)
  | Formula.scope _ none inner => 
    dbg_trace s!"[Level {level}] Found unquantified scope"
    getFormulaScopes inner (level + 1))

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (
  getRequiredVarsForPredicate
  getPredicatesFromFormula 
  getFormulaScopes)
