import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Types
import Mrs.PwlTransformMinScoping_Core
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open Lean (Format HashMap)

def checkScopeDependency (ep : EP) (scope : ScopeInfo) : Bool :=
  ep.rargs.any fun arg => scope.boundVars.contains arg.2 && arg.2.sort == 'x'

def checkNegationDependency (ep : EP) (scope : ScopeInfo) : Bool :=
  match scope.negVar with
  | some nv => 
    let deps := ep.rargs.any fun arg => arg.2 == nv
    dbg_trace s!"shouldStayAtOwnScope: negation scope check result: {deps}"
    deps
  | none => 
    dbg_trace "shouldStayAtOwnScope: no negation variable found"
    false

def shouldStayAtOwnScope (ep : ScopedEP) (scopes : List ScopeInfo) : Bool := 
  dbg_trace s!"shouldStayAtOwnScope checking predicate: {ep.predicate.predicate}"
  match ep.scope with
  | none => 
    dbg_trace "shouldStayAtOwnScope: no scope, allowing movement"
    false 
  | some scopeVar =>
    dbg_trace s!"shouldStayAtOwnScope: found scope {scopeVar}"
    if isRstrVar scopeVar || isBodyVar scopeVar then
      dbg_trace s!"shouldStayAtOwnScope: keeping due to guard var: RSTR={isRstrVar scopeVar} BODY={isBodyVar scopeVar}"
      true
    else
      dbg_trace s!"shouldStayAtOwnScope: checking scopes: {scopes.map (fun s => s!"{s.predicate}[{s.scopeType}]")}"
      let res := scopes.any fun scope =>
        let checkRes := match scope.scopeType with
        | ScopeType.Definite => 
          let depRes := checkScopeDependency ep.predicate scope
          dbg_trace s!"shouldStayAtOwnScope: definite scope check result: {depRes}"
          depRes
        | ScopeType.Universal =>
          let depRes := checkScopeDependency ep.predicate scope
          dbg_trace s!"shouldStayAtOwnScope: universal scope check result: {depRes}"
          depRes
        | ScopeType.Indefinite =>
          let depRes := checkScopeDependency ep.predicate scope  
          dbg_trace s!"shouldStayAtOwnScope: indefinite scope check result: {depRes}"
          depRes
        | ScopeType.NeverNeg | ScopeType.RegNeg =>
          checkNegationDependency ep.predicate scope
        | _ => 
          dbg_trace "shouldStayAtOwnScope: other scope type, allowing movement"
          false
        checkRes
      dbg_trace s!"shouldStayAtOwnScope: final result for {ep.predicate.predicate}: {res}"
      res

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (shouldStayAtOwnScope)
