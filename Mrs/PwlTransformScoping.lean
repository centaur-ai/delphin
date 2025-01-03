import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared 
import Mrs.PwlTransformScopingCore
import Mrs.PwlTransformMinScoping_Variables
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.Scoping

open MRS (Var EP)
open MM (Multimap)
open PWL.Transform (Formula Stats addStat getOrderedQuantArgs)
open HOF (lastTwoChars)
open InsertionSort
open BEq
open PWL.Transform.ScopingCore (shouldEliminateHandle isSimpleNamed)
open Lean (HashMap)

def normalizePredicate (p : String) : String :=
  if p.startsWith "_" then p.drop 1 else p

def isHigherOrder (pred : String) : Bool :=
  pred == "colon_p_namely" || pred == "_colon_p_namely" ||
  pred == "neg" || pred == "_neg" ||
  pred == "never_a_1" || pred == "_never_a_1"

def isEventOrImplicit (v : Var) : Bool :=
  v.sort == 'e' || v.sort == 'i'

def isEventReferenced (ev : Var) (preds : List EP) : Bool :=
  preds.any fun p =>
    if isHigherOrder p.predicate then
      false 
    else
      p.rargs.any fun arg => arg.2 == ev && arg.2.sort == 'e'

def isHandleReferenced (h : Var) (preds : List EP) : Bool :=
  preds.any fun p => p.rargs.any fun arg => arg.2 == h

def collectScopeEvents (preds: List EP) : List Var :=
  preds.foldl (fun acc ep => 
    let events := ep.rargs.filter (fun arg => arg.2.sort == 'e') |>.map (·.2)
    let referenced := events.filter (fun ev => isEventReferenced ev preds)
    (acc ++ referenced).eraseDups
  ) []

def processQuantifierEvents (rstrPreds : List EP) (bodyPreds : List EP) : 
    (List Var × List Var × List Var) :=
  let rstrEvents := collectScopeEvents rstrPreds
  let bodyEvents := collectScopeEvents bodyPreds
  
  -- Find events used in both scopes
  let sharedEvents := rstrEvents.filter (fun ev => bodyEvents.contains ev)
  
  -- Find events used only in one scope
  let rstrOnlyEvents := rstrEvents.filter (fun ev => !(bodyEvents.contains ev))
  let bodyOnlyEvents := bodyEvents.filter (fun ev => !(rstrEvents.contains ev))
  
  (sharedEvents, rstrOnlyEvents, bodyOnlyEvents)

def buildQuantifierFormula (quantType : String) (arg0 : Var) (rstrFormula : Formula) 
    (bodyFormula : Formula) (sharedEvents : List Var) (rstrEvents : List Var) 
    (bodyEvents : List Var) : Formula :=
  -- Build inner parts first with local scoping
  let scopedRstr := if rstrEvents.isEmpty then 
    rstrFormula
  else
    Formula.scope rstrEvents none rstrFormula

  let scopedBody := if bodyEvents.isEmpty then
    bodyFormula
  else  
    Formula.scope bodyEvents none bodyFormula

  -- Then build quantifier with shared event scope
  let guardedRstr := Formula.scope [] (some "rstr_guard") scopedRstr
  let guardedBody := Formula.scope [] (some "body_guard") scopedBody
  let inner := Formula.conj [guardedRstr, guardedBody]

  if sharedEvents.isEmpty then
    Formula.scope [arg0] (some quantType) inner
  else
    Formula.scope sharedEvents none $
      Formula.scope [arg0] (some quantType) inner

mutual

partial def processPredicates (parent : Var) (eps : List EP) (seenHandles : List Var) 
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) (inQuant : Bool := false) : (Option Formula × Stats) :=
  dbg_trace s!"RECURSE: processPredicates parent={parent} eps={eps.map (fun p => (p.predicate, p.label))}"
  match eps with
  | [] => (some (Formula.conj []), stats)
  | [ep] => 
    match processEP parent ep seenHandles hm stats ev with
    | (some formula, stats1) =>
      -- Only collect events when not in a quantifier
      if inQuant then
        (some formula, stats1)
      else
        let events := collectScopeEvents [ep]
        let result := if events.isEmpty then formula 
          else Formula.scope events none formula
        (some result, stats1)
    | (none, stats1) => (none, stats1)
  | eps => 
    match processEPs parent eps seenHandles hm stats ev with
    | (formulas, finalStats) =>
      match formulas with
      | [] => (some (Formula.conj []), finalStats)
      | [f] => 
        if inQuant then
          (some f, finalStats)
        else
          let events := collectScopeEvents eps
          let result := if events.isEmpty then f
            else Formula.scope events none f
          (some result, finalStats)
      | fs => 
        let filtered := fs.filter (fun f => !f.isEmptyConj)
        if inQuant then
          (some (Formula.conj filtered), finalStats)
        else
          -- Scope any event variables used at this level
          let events := collectScopeEvents eps
          let formula := Formula.conj filtered
          let result := if events.isEmpty then formula
            else Formula.scope events none formula
          (some result, finalStats)

partial def processEPs (parent : Var) (eps : List EP) (seenHandles : List Var)
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (List Formula × Stats) :=
  eps.foldl (fun (acc, stats) ep =>
    match processEP parent ep seenHandles hm stats ev with
    | (some formula, newStats) => 
      let newAcc := if formula.isEmptyConj then acc else acc ++ [formula]
      (newAcc, newStats)
    | (none, newStats) => (acc, newStats)) ([], stats)

partial def processEP (parent : Var) (ep : EP) (seenHandles : List Var)
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
  dbg_trace s!"RECURSE: processEP parent={parent} ep={ep.predicate}({ep.label})"
  
  if seenHandles.contains ep.label || shouldEliminateHandle hm ev ep.label then
    (none, stats)
  else
    let newSeen := ep.label :: seenHandles
    let normalized := normalizePredicate ep.predicate
    
    match normalized with
    | "neg" | "never_a_1" =>
      match ep.rargs.find? (fun arg => arg.1 == "ARG1"), ep.rargs.find? (fun arg => arg.1 == "ARG0") with
      | some (_, handle), some (_, evar) =>
        let innerPreds := hm.find? handle |>.getD []
        let isEvarReferenced := isEventReferenced evar innerPreds
        match processPredicates ep.label innerPreds newSeen hm stats ev true with
        | (none, stats1) => (none, stats1)
        | (some inner, stats1) =>
          let negFormula := if isEvarReferenced then
            Formula.scope [evar] (some ep.predicate) inner
          else
            inner
          (some negFormula, addStat stats1 2)
      | _, _ => (none, stats)
    
    | "therefore_a_1" =>
      -- Get the handle argument
      match ep.rargs.find? (fun arg => arg.1 == "ARG1") with
      | none => (some (Formula.atom ep), stats)
      | some (_, handle) =>
        match hm.find? handle with
        | none => (none, stats)
        | some preds =>
          -- Get content of handle
          match preds.head? with
          | none => (none, stats)
          | some handleEP =>
            -- Extract implicit variables, unknown variables, and event variables
            let implicitVars := ep.rargs.filter (fun arg => arg.2.sort == 'i') |>.map (·.2)
            let unknownVars := handleEP.rargs.filter (fun arg => arg.2.sort == 'u') |>.map (·.2)
            let eventVars := handleEP.rargs.filter (fun arg => arg.2.sort == 'e') |>.map (·.2)
            -- Build formula combining therefore_a_1 (without handle ref) with expanded handle content
            let cleanedEP := { ep with rargs := ep.rargs.filter (fun arg => arg.2.sort != 'h') }
            let baseFormula := Formula.atom cleanedEP
            let handleFormula := Formula.atom handleEP
            let combined := Formula.conj [baseFormula, handleFormula]
            -- Scope all collected variables
            let allVars := (implicitVars ++ unknownVars ++ eventVars).eraseDups
            let scopedFormula := if allVars.isEmpty then combined
                                else Formula.scope allVars none combined
            (some scopedFormula, stats)
    
    | "colon_p_namely" =>
      match ep.rargs.find? (fun arg => arg.1 == "ARG0"), 
            ep.rargs.find? (fun arg => arg.1 == "ARG1"), 
            ep.rargs.find? (fun arg => arg.1 == "ARG2") with
      | some (_, evar), some (_, handle1), some (_, handle2) =>
        let preds1 := hm.find? handle1 |>.getD []
        let preds2 := hm.find? handle2 |>.getD []
        let isEvarReferenced := isEventReferenced evar (preds1 ++ preds2)
        match processPredicates handle1 preds1 newSeen hm stats ev true,
              processPredicates handle2 preds2 newSeen hm stats ev true with
        | (some part1, stats1), (some part2, stats2) =>
          let conj := Formula.conj [part1, part2]
          let colonFormula := if isEvarReferenced then
            Formula.scope [evar] (some ep.predicate) conj
          else
            conj
          (some colonFormula, addStat stats2 4)
        | _, _ => (none, stats)
      | _, _, _ => (none, stats)

    | p =>
      if p == "the_q" || lastTwoChars p == "_q" then
        match getOrderedQuantArgs ep.rargs with
        | none => (none, stats)
        | some (arg0, rstr, body) =>
          let rstrPreds := hm.find? rstr |>.getD []
          let bodyPreds := hm.find? body |>.getD []
          
          match processPredicates ep.label rstrPreds newSeen hm stats ev true,
                processPredicates ep.label bodyPreds newSeen hm stats ev true with
          | (some rstrFormula, stats1), (some bodyFormula, stats2) =>
            let (sharedEvents, rstrEvents, bodyEvents) := 
              processQuantifierEvents rstrPreds bodyPreds

            -- Skip RSTR guard if there were no RSTR predicates
            let noRstr := rstrPreds.isEmpty && !isHandleReferenced rstr bodyPreds
              
            let formula := if noRstr then
              -- Just wrap the body formula in the quantifier 
              if sharedEvents.isEmpty then
                Formula.scope [arg0] (some p) bodyFormula
              else
                Formula.scope sharedEvents none $
                  Formula.scope [arg0] (some p) bodyFormula
            else
              buildQuantifierFormula p arg0 rstrFormula bodyFormula 
                sharedEvents rstrEvents bodyEvents

            (some formula, addStat stats2 3)
          | _, _ => (none, stats)
      else 
        (some (Formula.atom ep), stats)

end

end PWL.Transform.Scoping

export PWL.Transform.Scoping (processEP processPredicates normalizePredicate)
