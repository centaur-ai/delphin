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
      p.rargs.any fun arg => arg.2 == ev && (arg.2.sort == 'e' || arg.2.sort == 'i')

def isHandleReferenced (h : Var) (preds : List EP) : Bool :=
  preds.any fun p => p.rargs.any fun arg => arg.2 == h

def collectScopeEvents (preds: List EP) : List Var :=
  preds.foldl (fun acc ep => 
    let events := ep.rargs.filter (fun arg => arg.2.sort == 'e' || arg.2.sort == 'i') |>.map (·.2)
    let referenced := events.filter (fun ev => isEventReferenced ev preds)
    (acc ++ referenced).eraseDups
  ) []

def processQuantifierEvents (rstrPreds : List EP) (bodyPreds : List EP) : 
    (List Var × List Var × List Var) :=
  dbg_trace s!"QUANT_EVENTS: Processing RSTR({rstrPreds.map (·.predicate)}) BODY({bodyPreds.map (·.predicate)})"
  let rstrEvents := collectScopeEvents rstrPreds
  let bodyEvents := collectScopeEvents bodyPreds
  
  dbg_trace s!"QUANT_EVENTS: Initial events RSTR={rstrEvents} BODY={bodyEvents}"
  
  -- Find events used in both scopes
  let sharedEvents := rstrEvents.filter (fun ev => bodyEvents.contains ev)
  
  -- Find events used only in one scope
  let rstrOnlyEvents := rstrEvents.filter (fun ev => !(bodyEvents.contains ev))
  let bodyOnlyEvents := bodyEvents.filter (fun ev => !(rstrEvents.contains ev))
  
  dbg_trace s!"QUANT_EVENTS: Final shared={sharedEvents} rstrOnly={rstrOnlyEvents} bodyOnly={bodyOnlyEvents}"
  (sharedEvents, rstrOnlyEvents, bodyOnlyEvents)

def buildQuantifierFormula (quantType : String) (arg0 : Var) (rstrFormula : Formula) 
    (bodyFormula : Formula) (sharedEvents : List Var) (rstrEvents : List Var) 
    (bodyEvents : List Var) : Formula :=
  dbg_trace s!"BUILD_QUANT: {quantType} starting with RSTR events={rstrEvents} BODY events={bodyEvents}"

  -- Add event scoping for both the_q and non-the_q cases
  let scopedRstr := if rstrEvents.isEmpty then
    rstrFormula
  else
    Formula.scope rstrEvents none rstrFormula

  -- For both the_q and non-the_q, add body event scoping
  let scopedBody := if bodyEvents.isEmpty then
    bodyFormula
  else
    Formula.scope bodyEvents none bodyFormula

  dbg_trace s!"BUILD_QUANT: scopedRstr={scopedRstr}"
  dbg_trace s!"BUILD_QUANT: scopedBody={scopedBody}"

  -- Build inner formula based on quantifier type
  let inner := if quantType == "the_q" then
    -- Use guard structure for the_q
    let guardedRstr := Formula.scope rstrEvents (some "rstr_guard") scopedRstr
    let guardedBody := Formula.scope bodyEvents (some "body_guard") scopedBody
    Formula.conj [guardedRstr, guardedBody]
  else
    -- Regular conjunction for other quantifiers, events already scoped above
    Formula.conj [scopedRstr, scopedBody]

  dbg_trace s!"BUILD_QUANT: inner={inner}"

  let result := if sharedEvents.isEmpty then
    Formula.scope [arg0] (some quantType) inner
  else
    Formula.scope sharedEvents none $
      Formula.scope [arg0] (some quantType) inner
      
  dbg_trace s!"BUILD_QUANT: Final result={result}"
  result

mutual

partial def processPredicates (parent : Var) (eps : List EP) (seenHandles : List Var) 
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) 
    (scopedVars : List Var := []) (inQuant : Bool := false) : (Option Formula × Stats) :=
  dbg_trace s!"PREDICATES: Processing {eps.length} preds under parent={parent} inQuant={inQuant}"
  dbg_trace s!"PREDICATES: Preds are {eps.map (fun p => (p.predicate, p.label))}"
  match eps with
  | [] => (some (Formula.conj []), stats)
  | [ep] => 
    dbg_trace s!"PRED_SINGLE: Processing {ep.predicate} inQuant={inQuant}"
    let epEvents := ep.rargs.filter (fun arg => arg.2.sort == 'e') |>.map (·.2)
    dbg_trace s!"PRED_SINGLE: Has events {epEvents}"
    match processEP parent ep seenHandles hm stats ev scopedVars inQuant with
    | (some formula, stats1) =>
      dbg_trace s!"PRED_SINGLE: Got formula result={formula}"
      if inQuant then
        if epEvents.isEmpty then
          (some formula, stats1)
        else
          (some formula, stats1)
      else
        (some formula, stats1)
    | (none, stats1) => (none, stats1)
  | eps => 
    match processEPs parent eps seenHandles hm stats ev scopedVars inQuant with
    | (formulas, finalStats) =>
      match formulas with
      | [] => (some (Formula.conj []), finalStats)
      | [f] => (some f, finalStats)  
      | fs => 
        let filtered := fs.filter (fun f => !f.isEmptyConj)
        let formula := Formula.conj filtered
        dbg_trace s!"PREDICATES: Multiple preds with events raw formula={formula}"
        (some formula, finalStats)

partial def processEPs (parent : Var) (eps : List EP) (seenHandles : List Var)
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars)
    (scopedVars : List Var := []) (inQuant : Bool := false) : (List Formula × Stats) :=
  eps.foldl (fun (acc, stats) ep =>
    match processEP parent ep seenHandles hm stats ev scopedVars inQuant with
    | (some formula, newStats) => 
      let newAcc := if formula.isEmptyConj then acc else acc ++ [formula]
      (newAcc, newStats)
    | (none, newStats) => (acc, newStats)) ([], stats)

partial def processEP (parent : Var) (ep : EP) (seenHandles : List Var)
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) 
    (scopedVars : List Var := []) (inGuard : Bool := false) : (Option Formula × Stats) :=
  if seenHandles.contains ep.label || shouldEliminateHandle hm ev ep.label then
    (none, stats)
  else
    let newSeen := ep.label :: seenHandles
    let normalized := normalizePredicate ep.predicate
    
    match normalized with
    | "neg" | "never_a_1" => 
      match ep.rargs.find? (fun p => p.1 == "ARG1") with 
      | none => (none, stats)
      | some (_, handle) =>
        match hm.find? handle with
        | none => (none, stats)
        | some preds =>
          match processPredicates handle preds newSeen hm stats ev scopedVars true with
          | (some inner, stats1) => 
            -- Use appropriate scope label based on predicate
            let scopeLabel := if normalized == "never_a_1" then "never_a_1" else "neg"
            (some (Formula.scope [] (some scopeLabel) inner), stats1)
          | (none, stats1) => (none, stats1)

    | "colon_p_namely" =>
      match ep.rargs.find? (fun p => p.1 == "ARG0"),
            ep.rargs.find? (fun p => p.1 == "ARG1"), 
            ep.rargs.find? (fun p => p.1 == "ARG2") with
      | some (_, evar), some (_, handle1), some (_, handle2) =>
        let preds1 := hm.find? handle1 |>.getD []
        let preds2 := hm.find? handle2 |>.getD []
        match processPredicates handle1 preds1 newSeen hm stats ev scopedVars true,
              processPredicates handle2 preds2 newSeen hm stats ev scopedVars true with
        | (some part1, stats1), (some part2, stats2) =>
          let formula := Formula.scope [evar] (some "colon_p_namely") (Formula.conj [part1, part2])
          (some formula, addStat stats2 4)
        | _, _ => (none, stats)
      | _, _, _ => (none, stats)

    | p =>
      if lastTwoChars p == "_q" then
        match getOrderedQuantArgs ep.rargs with
        | none => (none, stats)
        | some (arg0, rstr, body) =>
          let rstrPreds := hm.find? rstr |>.getD []
          let bodyPreds := hm.find? body |>.getD []
          
          match processPredicates ep.label rstrPreds newSeen hm stats ev scopedVars true,
                processPredicates ep.label bodyPreds newSeen hm stats ev scopedVars true with
          | (some rstrFormula, stats1), (some bodyFormula, stats2) =>
            let rstrEvents := rstrPreds.foldl (fun acc p => 
              acc ++ (p.rargs.filter (fun arg => 
                (arg.2.sort == 'e' || arg.2.sort == 'i') && !(scopedVars.contains arg.2)) |>.map (·.2))) [] |>.eraseDups
            let bodyEvents := bodyPreds.foldl (fun acc p => 
              acc ++ (p.rargs.filter (fun arg => 
                (arg.2.sort == 'e' || arg.2.sort == 'i') && !(scopedVars.contains arg.2)) |>.map (·.2))) [] |>.eraseDups

            let guardedRstr := Formula.scope rstrEvents (some "rstr_guard") rstrFormula
            let guardedBody := Formula.scope bodyEvents (some "body_guard") bodyFormula
            
            -- Special case for no_q
            if p == "no_q" || p == "_no_q" then
              (some (Formula.scope [arg0] (some "no_q") (Formula.conj [guardedRstr, guardedBody])), stats2)
            else
              (some (Formula.scope [arg0] (some p) (Formula.conj [guardedRstr, guardedBody])), stats2)
          | _, _ => (none, stats)
      
      else 
        if inGuard then
          -- Already in a guard, just return the predicate
          (some (Formula.atom ep), stats)
        else
          -- Not in a guard, ensure events are scoped
          let eventVars := ep.rargs.filter (fun arg => 
            (arg.2.sort == 'e' || arg.2.sort == 'i') && !(scopedVars.contains arg.2)) |>.map (·.2)
          match eventVars with
          | [] => (some (Formula.atom ep), stats)
          | evs => (some (Formula.scope evs none (Formula.atom ep)), stats)

end

end PWL.Transform.Scoping

export PWL.Transform.Scoping (processEP processPredicates normalizePredicate)
