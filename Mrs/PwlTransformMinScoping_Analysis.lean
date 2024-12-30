import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (EP Var)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

partial def analyzeFormula (f : Formula) : (List ScopeInfo × List ScopedEP) :=
  dbg_trace "MINSCOPE:analyzeFormula starting"

  let rec analyze (f : Formula) (curScope : Option Var) (acc : List ScopeInfo × List ScopedEP) : (List ScopeInfo × List ScopedEP) :=
    dbg_trace s!"MINSCOPE:analyze formula=({match f with | Formula.atom ep => s!"atom({ep.predicate})" | Formula.scope _ _ _ => "scope" | Formula.conj fs => s!"conj(len={fs.length})"}) curScope={curScope}"
    
    match f with
    | Formula.atom ep => 
      let (scopes, preds) := acc
      if containsEP preds ep then
        dbg_trace s!"MINSCOPE:  Already processed predicate: {ep.predicate}"
        (scopes, preds)
      else
        dbg_trace s!"MINSCOPE:  Adding predicate {ep.predicate} with scope {curScope}"
        (scopes, { predicate := ep, scope := curScope } :: preds)
        
    | Formula.scope vars (some "rstr_guard") inner =>
      dbg_trace s!"MINSCOPE:  Found RSTR guard scope with vars: {vars}"
      (match vars with
      | [] => 
        dbg_trace "MINSCOPE:    ERROR: Empty RSTR guard vars"
        unreachable!
      | rvar :: _ =>
        let newScope := {
          predicate := "rstr_guard",
          boundVars := vars,
          scopeType := ScopeType.RstrGuard
        }
        dbg_trace s!"MINSCOPE:    Created RSTR guard scope: {newScope.predicate} boundVars={newScope.boundVars}"
        let result := analyze inner (some rvar) (newScope :: acc.1, acc.2)
        dbg_trace s!"MINSCOPE:    RSTR guard analysis complete with scopes: {result.1.map (fun s => s.predicate)}"
        result)
        
    | Formula.scope vars (some quant) inner =>
      dbg_trace s!"MINSCOPE:  Found quantifier scope: {quant} with vars={vars}"
      let nextId := match curScope with
                   | none => 1
                   | some v => v.id + 1
      let newScope := Var.mk nextId 'h' #[] 
      let normalized := if quant.startsWith "_" then quant.drop 1 else quant
      let scopeType := 
        if normalized == "every_q" then (
          dbg_trace "MINSCOPE:    Creating UNIVERSAL scope"
          ScopeType.Universal
        ) else if normalized == "the_q" || normalized == "def_explicit_q" then (
          dbg_trace "MINSCOPE:    Creating THE_Q scope"
          ScopeType.Definite
        ) else if normalized == "never_a_1" then
          ScopeType.NeverNeg
        else if normalized == "neg" then
          ScopeType.RegNeg
        else if normalized == "colon_p_namely" then
          ScopeType.ColonNamely
        else
          ScopeType.Indefinite
      let newScopeInfo : ScopeInfo := {
        predicate := normalized,
        boundVars := orderVarsForScoping vars.eraseDups,
        scopeType := scopeType,
        negVar := if vars.isEmpty then none else some vars.head!
      }
      dbg_trace s!"MINSCOPE:    Created scope info: {newScopeInfo.predicate} type={toString newScopeInfo.scopeType} boundVars={newScopeInfo.boundVars} negVar={newScopeInfo.negVar}"
      let result := analyze inner (some newScope) (newScopeInfo :: acc.1, acc.2)
      dbg_trace s!"MINSCOPE:    Regular scope analysis complete with scopes: {result.1.map (fun s => s.predicate)}"
      result
      
    | Formula.scope vars none inner =>
      dbg_trace s!"MINSCOPE:  Found unnamed scope with vars: {vars}"
      analyze inner curScope acc
      
    | Formula.conj fs =>
      dbg_trace s!"MINSCOPE:  Processing conjunction with {fs.length} formulas: {fs.map (fun f => match f with | Formula.atom ep => ep.predicate | Formula.scope _ _ _ => "scope" | Formula.conj _ => "conj")}"
      fs.foldl (fun acc f => analyze f curScope acc) acc

  let ret := analyze f none ([], [])
  dbg_trace s!"MINSCOPE:analyzeFormula complete\n  Scopes: {ret.1.map (fun s => s!"{s.predicate}[{s.scopeType}]")}\n  Predicates: {ret.2.map (fun p => s!"{p.predicate.predicate}[scope={p.scope}]")}"
  ret

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (analyzeFormula)
