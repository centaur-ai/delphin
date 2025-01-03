import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared 
import Mrs.PwlTransformScopingCore
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

mutual 
partial def processPredicates (parent : Var) (eps : List EP) (seenHandles : List Var) 
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
  dbg_trace s!"RECURSE: processPredicates parent={parent} eps={eps.map (fun p => (p.predicate, p.label))}"
  dbg_trace s!"RECURSE: seen handles={seenHandles}"
  match eps with
  | [] => 
    dbg_trace s!"RECURSE: empty eps for parent={parent}"
    (some (Formula.conj []), stats)
  | [ep] => 
    dbg_trace s!"RECURSE: single EP {(ep.predicate, ep.label)} for parent={parent}"
    processEP parent ep seenHandles hm stats ev
  | eps =>
    dbg_trace s!"RECURSE: multiple EPs for parent={parent}: {eps.map (fun p => (p.predicate, p.label))}"
    match processEPs parent eps seenHandles hm stats ev with
    | (formulas, finalStats) =>
      match formulas with
      | [] => 
        dbg_trace s!"RECURSE: no formulas generated for parent={parent}"
        (some (Formula.conj []), finalStats)
      | fs => 
        dbg_trace s!"RECURSE: generated formulas for parent={parent}: {fs}"
        (some (Formula.conj fs), finalStats)

partial def processEPs (parent : Var) (eps : List EP) (seenHandles : List Var)
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (List Formula × Stats) :=
  eps.foldl (fun (acc, stats) ep =>
    match processEP parent ep seenHandles hm stats ev with
    | (some formula, newStats) => (acc ++ [formula], newStats) 
    | (none, newStats) => (acc, newStats)) ([], stats)

partial def processEP (parent : Var) (ep : EP) (seenHandles : List Var)
    (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
  dbg_trace s!"RECURSE: processEP parent={parent} ep={ep.predicate}({ep.label}) args={ep.rargs}"
  dbg_trace s!"RECURSE: current seen handles={seenHandles}"
  
  if seenHandles.contains ep.label || shouldEliminateHandle hm ev ep.label then
    dbg_trace s!"RECURSE: skipping {ep.label} - already seen or eliminated"
    (none, stats)
  else
    let newSeen := ep.label :: seenHandles
    let normalized := normalizePredicate ep.predicate
    
    match normalized with
    | "neg" | "never_a_1" =>
      dbg_trace s!"RECURSE: processing negation at {ep.label}"
      match ep.rargs.find? (fun arg => arg.1 == "ARG1"), ep.rargs.find? (fun arg => arg.1 == "ARG0") with
      | some (_, handle), some (_, evar) =>
        let innerPreds := hm.find? handle |>.getD []
        match processPredicates ep.label innerPreds newSeen hm stats ev with
        | (none, stats1) => (none, stats1)
        | (some inner, stats1) =>
          (some (Formula.scope [evar] (some ep.predicate) inner), addStat stats1 2)
      | _, _ => (none, stats)
    
    | "colon_p_namely" =>
      dbg_trace s!"RECURSE: processing colon_p_namely at {ep.label}"
      match ep.rargs.find? (fun arg => arg.1 == "ARG0"), 
            ep.rargs.find? (fun arg => arg.1 == "ARG1"), 
            ep.rargs.find? (fun arg => arg.1 == "ARG2") with
      | some (_, evar), some (_, handle1), some (_, handle2) =>
        let innerPreds1 := hm.find? handle1 |>.getD []
        let innerPreds2 := hm.find? handle2 |>.getD []
        match processPredicates handle1 innerPreds1 newSeen hm stats ev with
        | (none, stats1) => (none, stats1)
        | (some part1, stats1) =>
          match processPredicates handle2 innerPreds2 newSeen hm stats1 ev with
          | (none, stats2) => (none, stats2)
          | (some part2, stats2) =>
            (some (Formula.scope [evar] (some ep.predicate) (Formula.conj [part1, part2])), addStat stats2 4)
      | _, _, _ => (none, stats)

    | "the_q" =>
      dbg_trace s!"RECURSE: processing the_q at {ep.label}"
      match getOrderedQuantArgs ep.rargs with
      | none => (none, stats)
      | some (arg0, rstr, body) =>
        -- let rstrVar := {id := arg0.id, sort := 'r', props := #[]}
        -- let bodyVar := {id := arg0.id, sort := 'b', props := #[]}
        let rstrPreds := hm.find? rstr |>.getD []
        let bodyPreds := hm.find? body |>.getD []
        match processPredicates ep.label rstrPreds newSeen hm stats ev with
        | (none, stats1) => (none, stats1)
        | (some rstrFormula, stats1) =>
          match processPredicates ep.label bodyPreds newSeen hm stats1 ev with
          | (none, stats2) => (none, stats2)
          | (some bodyFormula, stats2) =>
            let formula := Formula.scope [arg0] (some "the_q") (Formula.conj [
              -- Formula.scope [rstrVar] (some "rstr_guard") rstrFormula,
              -- Formula.scope [bodyVar] (some "body_guard") bodyFormula
              Formula.scope [] (some "rstr_guard") rstrFormula,
              Formula.scope [] (some "body_guard") bodyFormula
            ])
            (some formula, addStat stats2 3)

    | p =>
      if lastTwoChars p == "_q" then
        dbg_trace s!"RECURSE: processing quantifier {p} at {ep.label}"
        match getOrderedQuantArgs ep.rargs with
        | none => (none, stats)
        | some (arg0, rstr, body) =>
          let rstrPreds := hm.find? rstr |>.getD []
          let bodyPreds := hm.find? body |>.getD []
          match processPredicates ep.label rstrPreds newSeen hm stats ev with
          | (none, stats1) => (none, stats1)
          | (some rstrFormula, stats1) =>
            match processPredicates ep.label bodyPreds newSeen hm stats1 ev with
            | (none, stats2) => (none, stats2)
            | (some bodyFormula, stats2) =>
              (some (Formula.scope [arg0] (some p) (Formula.conj [rstrFormula, bodyFormula])),
               addStat stats2 3)
      else 
        dbg_trace s!"RECURSE: atomic predicate {p} at {ep.label}"
        (some (Formula.atom ep), stats)

end

end PWL.Transform.Scoping

export PWL.Transform.Scoping (processEP processPredicates normalizePredicate)
