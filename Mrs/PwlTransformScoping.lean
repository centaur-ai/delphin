import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared 
import Mrs.Hof
import Mrs.PwlTransformScopingCore
import Util.InsertionSort

namespace PWL.Transform.Scoping

open MRS (Var EP)
open MM (Multimap)
open PWL.Transform (Formula Stats addStat getOrderedQuantArgs)
open HOF (lastTwoChars)
open InsertionSort
open BEq
open PWL.Transform.ScopingCore

def normalizePredicate (p : String) : String :=
  if p.startsWith "_" then p.drop 1 else p

mutual

partial def processPredicates (parent : Var) (eps : List EP) (seenHandles : List Var) 
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
  match eps with
  | [] => (some (Formula.conj []), stats)
  | [ep] => processEP parent ep seenHandles hm stats ev
  | eps =>
    match processEPs parent eps seenHandles hm stats ev with
    | (formulas, finalStats) =>
      match formulas with
      | [] => (some (Formula.conj []), finalStats)
      | fs => (some (Formula.conj fs), finalStats)

partial def processEPs (parent : Var) (eps : List EP) (seenHandles : List Var)
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (List Formula × Stats) :=
  eps.foldl (fun (acc, stats) ep =>
    match processEP parent ep seenHandles hm stats ev with
    | (some formula, newStats) => (acc ++ [formula], newStats) 
    | (none, newStats) => (acc, newStats)) ([], stats)

partial def processEP (parent : Var) (ep : EP) (seenHandles : List Var)
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
  dbg_trace s!"processEP starting with:\n  parent: {parent}\n  ep: {ep}\n  seen handles: {seenHandles}"
  
  if seenHandles.contains ep.label || shouldEliminateHandle hm ev ep.label then
    dbg_trace "  skipping due to seen/eliminated handle"
    (none, stats)
  else
    let newSeen := ep.label :: seenHandles
    let normalized := normalizePredicate ep.predicate
    
    (match normalized with
    | "neg" | "never_a_1" =>
      dbg_trace "Processing negation predicate"
      dbg_trace s!"  at handle: {ep.label}"
      dbg_trace s!"  with args: {ep.rargs}"
      dbg_trace s!"  parent handle: {parent}"
      (match ep.rargs.find? (fun arg => arg.1 == "ARG1"), ep.rargs.find? (fun arg => arg.1 == "ARG0") with
      | some (_, handle), some (_, evar) =>
        dbg_trace s!"  neg handle arg: {handle}"
        dbg_trace s!"  neg event arg: {evar}"
        let innerPreds := hm.find? handle |>.getD []
        dbg_trace s!"  inner preds for negation: {innerPreds}"
        (match processPredicates ep.label innerPreds newSeen hm stats ev with
        | (none, stats1) => (none, stats1)
        | (some inner, stats1) =>
          dbg_trace s!"  negation inner formula: {inner}"
          (some (Formula.scope [evar] (some ep.predicate) inner), addStat stats1 2))
      | _, _ => 
        dbg_trace "Missing required args for negation"
        (none, stats))
    
    | "colon_p_namely" =>
      dbg_trace "Processing colon_p_namely predicate"
      dbg_trace s!"  at handle: {ep.label}"
      dbg_trace s!"  with args: {ep.rargs}"
      (match ep.rargs.find? (fun arg => arg.1 == "ARG0"), 
             ep.rargs.find? (fun arg => arg.1 == "ARG1"), 
             ep.rargs.find? (fun arg => arg.1 == "ARG2") with
      | some (_, evar), some (_, handle1), some (_, handle2) =>
        let innerPreds1 := hm.find? handle1 |>.getD []
        let innerPreds2 := hm.find? handle2 |>.getD []
        (match processPredicates handle1 innerPreds1 newSeen hm stats ev with
        | (none, stats1) => (none, stats1)
        | (some part1, stats1) =>
          (match processPredicates handle2 innerPreds2 newSeen hm stats1 ev with
          | (none, stats2) => (none, stats2)
          | (some part2, stats2) =>
            (some (Formula.scope [evar] (some ep.predicate) (Formula.conj [part1, part2])), addStat stats2 4)))
      | _, _, _ => 
        dbg_trace "  missing required arguments"
        (none, stats))

    | "the_q" =>
      (match getOrderedQuantArgs ep.rargs with
      | none =>
        dbg_trace s!"THE_Q: Failed to get quantifier args for {ep}"
        (none, stats)
      | some (arg0, rstr, body) =>
        dbg_trace s!"THE_Q: Got args ARG0={arg0} RSTR={rstr} BODY={body}"
        let rstrVar := {id := arg0.id, sort := 'r', props := #[]}
        dbg_trace s!"THE_Q: Created RSTR var {rstrVar} from {arg0}"
        let rstrPreds := hm.find? rstr |>.getD []
        let bodyPreds := hm.find? body |>.getD []
        dbg_trace s!"THE_Q: Found predicates RSTR={rstrPreds} BODY={bodyPreds}"
        (match processPredicates ep.label rstrPreds newSeen hm stats ev with
        | (none, stats1) =>
          dbg_trace s!"THE_Q: Failed to process RSTR predicates"
          (none, stats1)
        | (some rstrFormula, stats1) =>
          dbg_trace s!"THE_Q: Built RSTR formula {rstrFormula}"
          (match processPredicates ep.label bodyPreds newSeen hm stats1 ev with
          | (none, stats2) =>
            dbg_trace s!"THE_Q: Failed to process BODY predicates"
            (none, stats2)
          | (some bodyFormula, stats2) =>
            dbg_trace s!"THE_Q: Building final formula with RSTR guard for {arg0}"
            let formula := Formula.scope [arg0] (some "the_q") (Formula.conj [
              Formula.scope [rstrVar] (some "rstr_guard") rstrFormula,
              bodyFormula
            ])
            dbg_trace s!"THE_Q: Created formula {formula}"
            (some formula, addStat stats2 3))))

    | "temp_compound_name" =>
      dbg_trace s!"processEP: temp_compound_name with label {ep.label}"
      (match ep.rargs with
      | [("X1", x1), ("X2", x2), ("A", a), ("B", b)] =>
        let aPreds := hm.find? a |>.getD []
        let bPreds := hm.find? b |>.getD []
        (match processPredicates ep.label aPreds newSeen hm stats ev with
        | (none, stats1) => (none, stats1)
        | (some aFormula, stats1) =>
          (match processPredicates ep.label bPreds newSeen hm stats1 ev with
          | (none, stats2) => (none, stats2) 
          | (some bFormula, stats2) =>
            match ep.carg with
            | some name =>
              let namedEP := EP.mk "named" none ep.label [("ARG0", x1)] (some name)
              let rstr := Formula.atom namedEP
              let substitutedAFormula := if isSimpleNamed aFormula then
                Formula.conj []  -- Skip simple named predicate
              else 
                aFormula.substitute x2 x1
              let substitutedBFormula := bFormula.substitute x2 x1
              let body := Formula.conj [rstr, substitutedAFormula, substitutedBFormula]
              (some (Formula.scope [x1] (some "proper_q") body), addStat stats2 1)
            | none => (none, stats2)))
      | _ => 
        dbg_trace "Invalid temp_compound_name args"
        (none, stats))

    | p =>
      if lastTwoChars p == "_q" then
        dbg_trace s!"Found generic quantifier predicate: {p}"
        (match getOrderedQuantArgs ep.rargs with
        | none => (none, stats)
        | some (arg0, rstr, body) =>
          let rstrPreds := hm.find? rstr |>.getD []
          let bodyPreds := hm.find? body |>.getD []
          (match processPredicates ep.label rstrPreds newSeen hm stats ev with
          | (none, stats1) => (none, stats1)
          | (some rstrFormula, stats1) =>
            (match processPredicates ep.label bodyPreds newSeen hm stats1 ev with
            | (none, stats2) => (none, stats2)
            | (some bodyFormula, stats2) =>
              (some (Formula.scope [arg0] (some p) (Formula.conj [rstrFormula, bodyFormula])),
               addStat stats2 3))))
      else 
        dbg_trace "Processing non-quantifier predicate"
        (some (Formula.atom ep), stats))

end

end PWL.Transform.Scoping

export PWL.Transform.Scoping (processEP processPredicates normalizePredicate)
