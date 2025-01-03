import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Types
import Mrs.PwlTransformMinScoping_Core
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (EP Var)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

def newVarWithId (id : Nat) : Var :=
  { id := id, sort := 'h', props := #[] }

partial def analyzeFormula (f : Formula) : (List ScopeInfo × List ScopedEP) :=
  dbg_trace "MINSCOPE:analyzeFormula starting"

  let rec analyze (f : Formula) (curScope : Option Var) (ctx : Option ScopeType) 
      (acc : List ScopeInfo × List ScopedEP) : (List ScopeInfo × List ScopedEP) :=
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
      if ctx != some ScopeType.Definite then
        analyze inner curScope ctx acc
      else
        dbg_trace s!"MINSCOPE:  Found RSTR guard scope with vars: {vars}"
        match vars with
        | [] => 
          dbg_trace s!"MINSCOPE:  Processing empty RSTR guard"
          analyze inner curScope ctx acc
        | rvar :: _ =>
          let newScope : ScopeInfo := {
            predicate := "rstr_guard",
            boundVars := vars,
            scopeType := ScopeType.RstrGuard
          }
          dbg_trace s!"MINSCOPE:    Created RSTR guard scope"
          let result := analyze inner (some rvar) ctx (newScope :: acc.1, acc.2)
          dbg_trace s!"MINSCOPE:    RSTR guard analysis complete"
          result

    | Formula.scope vars (some "body_guard") inner =>
      if ctx != some ScopeType.Definite then
        analyze inner curScope ctx acc
      else
        dbg_trace s!"MINSCOPE:  Found BODY guard scope with vars: {vars}"
        match vars with
        | [] => 
          dbg_trace s!"MINSCOPE:  Processing empty BODY guard"
          analyze inner curScope ctx acc
        | bvar :: _ =>
          let newScope : ScopeInfo := {
            predicate := "body_guard",
            boundVars := vars,
            scopeType := ScopeType.BodyGuard
          }
          dbg_trace s!"MINSCOPE:    Created BODY guard scope"
          let result := analyze inner (some bvar) ctx (newScope :: acc.1, acc.2)
          dbg_trace s!"MINSCOPE:    BODY guard analysis complete"
          result
        
    | Formula.scope vars (some quant) inner =>
      dbg_trace s!"MINSCOPE:  Found quantifier scope: {quant} with vars={vars}"
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
      let nextId := match curScope with
                   | none => newVarWithId 1
                   | some v => newVarWithId (v.id + 1)
      let newScope : ScopeInfo := {
        predicate := normalized,
        boundVars := vars,
        scopeType := scopeType,
        negVar := if vars.isEmpty then none else some vars.head!
      }
      dbg_trace s!"MINSCOPE:    Created scope info"
      let result := analyze inner (some nextId) (some scopeType) (newScope :: acc.1, acc.2)
      dbg_trace s!"MINSCOPE:    Regular scope analysis complete"
      result
      
    | Formula.scope vars none inner =>
      dbg_trace s!"MINSCOPE:  Found unnamed scope with vars: {vars}"
      analyze inner curScope ctx acc
      
    | Formula.conj fs =>
      dbg_trace s!"MINSCOPE:  Processing conjunction"
      fs.foldl (fun acc f => analyze f curScope ctx acc) acc

  let ret := analyze f none none ([], [])
  dbg_trace s!"MINSCOPE:analyzeFormula complete"
  ret

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (analyzeFormula)
