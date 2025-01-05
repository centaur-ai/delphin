import Lean.Data.HashMap
import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Types
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.EqualityRemoval

open MRS (Var EP)
open Lean (HashMap)
open PWL.Transform
open BEq

inductive GuardType where
  | RstrGuard : GuardType
  | BodyGuard : GuardType
  deriving BEq, Inhabited

instance : ToString GuardType where
  toString 
  | GuardType.RstrGuard => "rstr"
  | GuardType.BodyGuard => "body"

instance : ToString (HashMap Var Var) where
  toString m := toString (m.toList)

structure SubstMap where
  substitutions : HashMap Var Var
  scopeStack : List Var
  currentGuard : Option GuardType
  deriving Inhabited

instance : ToString SubstMap where
  toString st := s!"SubstMap(subst: {st.substitutions}, stack: {st.scopeStack}, guard: {st.currentGuard})"

def emptyState : SubstMap := 
  { substitutions := HashMap.empty, scopeStack := [], currentGuard := none }

def SubstMap.enterScope (st : SubstMap) (v : Var) : SubstMap :=
  { st with scopeStack := v :: st.scopeStack }

def SubstMap.exitScope (st : SubstMap) : SubstMap :=
  { st with scopeStack := st.scopeStack.tail! }

def SubstMap.enterGuard (st : SubstMap) (g : GuardType) : SubstMap :=
  { st with currentGuard := some g }

def SubstMap.exitGuard (st : SubstMap) : SubstMap :=
  { st with currentGuard := none }

def SubstMap.addSubstitution (st : SubstMap) (oldVar newVar : Var) : SubstMap := 
  dbg_trace s!"SUBST: Adding {oldVar} → {newVar} stack={st.scopeStack} guard={st.currentGuard}"
  { st with substitutions := st.substitutions.insert oldVar newVar }

def SubstMap.substitute (st : SubstMap) (v : Var) : Var :=
  match st.substitutions.find? v with
  | some newVar => newVar  
  | none => v

def substituteVarList (st : SubstMap) (vars : List Var) : List Var :=
  vars.map (fun v => st.substitute v)

partial def cleanConjunction (fs : List Formula) : Formula :=
  let rec flatten (f : Formula) : List Formula := 
    match f with
    | Formula.conj nested => nested.foldl (fun acc f => acc ++ flatten f) []
    | other => [other]
  
  let flattened := fs.foldl (fun acc f => acc ++ flatten f) []
  
  let nonEmpty := flattened.filter fun f => match f with
    | Formula.conj [] => false
    | Formula.conj [Formula.conj []] => false
    | Formula.conj fs => !fs.all (·.isEmptyConj)
    | _ => !f.isEmptyConj

  let deduped := nonEmpty.foldl (fun acc f =>
    if acc.any (fun existing => existing == f) then acc
    else acc ++ [f]) []

  dbg_trace s!"CLEAN: flattened {fs.length} → {flattened.length} → {deduped.length} conjuncts"
  match deduped with
  | [] => Formula.conj []
  | [single] => single
  | multiple => Formula.conj multiple

def cleanFormula (f : Formula) : Formula :=
  match f with
  | Formula.conj fs => cleanConjunction fs
  | other => other

mutual
  partial def collectFormula (f : Formula) (st : SubstMap) : (Formula × SubstMap) :=
    match f with
    | Formula.atom ep =>
      match ep.predicate, ep.rargs with
      | "=", [(_, var1), (_, var2)] => 
        dbg_trace s!"EQUAL: {var1} = {var2} (stack={st.scopeStack}, guard={st.currentGuard})"
        if st.scopeStack.contains var2 then
          dbg_trace s!"EQUAL: {var1} → {var2} - var2 in outer scope"
          (Formula.conj [], st.addSubstitution var1 var2)
        else if st.scopeStack.contains var1 then
          dbg_trace s!"EQUAL: {var2} → {var1} - var1 in outer scope"
          (Formula.conj [], st.addSubstitution var2 var1)
        else
          dbg_trace "EQUAL: No substitution - neither var in outer scope"
          (Formula.atom ep, st)
      | _, _ => 
        dbg_trace s!"PRED: {ep.predicate}"
        let newArgs := ep.rargs.map fun (name, var) =>
          (name, st.substitute var)
        (Formula.atom { ep with rargs := newArgs }, st)

    | Formula.conj formulas =>
      dbg_trace s!"CONJ of {formulas.length} (guard={st.currentGuard})"
      let rec processFormulas (remaining : List Formula) (acc : List Formula) (state : SubstMap) : (List Formula × SubstMap) :=
        match remaining with
        | [] => (acc, state)
        | f :: fs =>
          let (newF, newState) := collectFormula f state
          match newF with
          | Formula.conj [] => processFormulas fs acc newState
          | _ => processFormulas fs (acc ++ [newF]) newState

      let (processed, finalState) := processFormulas formulas [] st
      match processed with
      | [] => (Formula.conj [], finalState)
      | [single] => (single, finalState)
      | multiple => (Formula.conj multiple, finalState)

    | Formula.scope vars quant inner =>
      match quant with
      | some "rstr_guard" =>
        dbg_trace s!"RSTR_GUARD[{vars}] start"
        let guardState := st.enterGuard GuardType.RstrGuard
        let (newInner, innerState) := collectFormula inner guardState
        let exitState := innerState.exitGuard
        let result := Formula.scope vars quant newInner
        dbg_trace s!"RSTR_GUARD[{vars}] = {result}"
        (result, exitState)

      | some "body_guard" =>
        dbg_trace s!"BODY_GUARD[{vars}] start"
        let guardState := st.enterGuard GuardType.BodyGuard
        let newVars := substituteVarList guardState vars
        let (newInner, innerState) := collectFormula inner guardState
        let exitState := innerState.exitGuard
        if newInner.isEmptyConj then
          (Formula.conj [], exitState)
        else
          let result := Formula.scope newVars quant newInner
          dbg_trace s!"BODY_GUARD[{vars}] = {result}"
          (result, exitState)

      | _ =>
        dbg_trace s!"SCOPE {quant}[{vars}] (guard={st.currentGuard})"
        let stWithScope := vars.foldl (fun acc v => acc.enterScope v) st
        let (newInner, stateAfterInner) := collectFormula inner stWithScope
        let finalState := vars.foldl (fun acc _ => acc.exitScope) stateAfterInner
        
        -- Check if any vars in this scope were substituted
        let substitutedVars := vars.filter (fun v => finalState.substitutions.contains v)
        if !substitutedVars.isEmpty then
          dbg_trace s!"SCOPE: Remove {quant}[{vars}] - vars {substitutedVars} were substituted"
          (cleanFormula newInner, finalState)
        else if newInner.isEmptyConj then 
          dbg_trace s!"SCOPE: Remove {quant}[{vars}] - empty inner"
          (Formula.conj [], finalState)
        else
          let result := Formula.scope vars quant newInner
          dbg_trace s!"SCOPE: End {quant}[{vars}]"
          (result, finalState)

end

def simplifyEqualities (f : Formula) : Formula :=
  dbg_trace "\n============= Starting equality simplification ============="
  let (collected, _) := collectFormula f emptyState
  dbg_trace "\n============= Completed equality simplification ============="
  collected

end PWL.Transform.EqualityRemoval

export PWL.Transform.EqualityRemoval (simplifyEqualities)
