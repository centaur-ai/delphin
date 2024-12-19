import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.Scoping

open MRS (EP Var)
open MM (Multimap)
open PWL.Transform (Formula)
open HOF (lastTwoChars)
open InsertionSort
open BEq

structure EliminatedVars where
  vars : List Var
  deriving Inhabited

def EliminatedVars.empty : EliminatedVars := 
  EliminatedVars.mk []

structure Stats where
  counts : Lean.HashMap Nat Nat := Lean.HashMap.empty
  deriving Inhabited

def orderPredicateArgs (args : List (String × Var)) : List (String × Var) :=
  args.filter (fun a => a.1.startsWith "ARG") |> insertionSort

def addStat (stats : Stats) (key : Nat) : Stats :=
  { counts := match stats.counts.find? key with
    | none => stats.counts.insert key 1
    | some n => stats.counts.insert key (n + 1) }

def isVarEliminated (ev : EliminatedVars) (v : Var) : Bool :=
  ev.vars.contains v

def shouldEliminateHandle (hm : Multimap Var EP) (ev : EliminatedVars) (handle : Var) : Bool :=
  match hm.find? handle with
  | none => unreachable!  
  | some eps =>
    eps.any fun ep =>
      ep.rargs.any fun (_, v) => isVarEliminated ev v

def collectEliminatedVars (preds : List EP) : EliminatedVars :=
  preds.foldl (fun acc ep =>
    if lastTwoChars ep.predicate == "_q" then
      match ep.rargs with
      | ("ARG0", v) :: _ => EliminatedVars.mk (v :: acc.vars)
      | _ => acc
    else acc
  ) EliminatedVars.empty

mutual
  partial def processPredicates (parent : Var) (eps : List EP) (seenHandles : List Var) 
      (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
    match eps with
    | [] => (some (Formula.conj []), stats)  -- Empty list gives empty conjunction
    | [ep] => processEP parent ep seenHandles hm stats ev
    | _ =>
      dbg_trace ("processPredicates for handle " ++ toString parent)
      dbg_trace ("  predicates: " ++ toString eps)
      dbg_trace ("  handleMap keys: " ++ toString hm.keys)
      match processEPs parent eps seenHandles hm stats ev with
      | (formulas, finalStats) =>
        dbg_trace ("  results: " ++ toString formulas)
        match formulas with
        | [] => (some (Formula.conj []), finalStats)  -- No valid formulas gives empty conjunction
        | fs => (some (Formula.conj fs), finalStats)

  partial def processEPs (parent : Var) (eps : List EP) (seenHandles : List Var)
      (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (List Formula × Stats) :=
    eps.foldl (fun (acc, stats) ep =>
      match processEP parent ep seenHandles hm stats ev with
      | (some formula, newStats) => (acc ++ [formula], newStats)
      | (none, newStats) => (acc, newStats)) ([], stats)

  partial def processEP (parent : Var) (ep : EP) (seenHandles : List Var)
      (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
    if seenHandles.contains ep.label || shouldEliminateHandle hm ev ep.label then
      (none, stats)
    else
      let newSeen := ep.label :: seenHandles
      dbg_trace s!"processEP: {ep.predicate} with label {ep.label}"
      match ep.predicate with 
      | "never_a_1" | "_never_a_1" =>
        match ep.rargs.find? (fun arg => arg.1 == "ARG1") with
        | none => (none, stats)
        | some (_, handle) =>
          match ep.rargs.find? (fun arg => arg.1 == "ARG0") with 
          | none => (none, stats)
          | some (_, id) =>
            let innerPreds := hm.find? handle |>.getD []
            match processPredicates ep.label innerPreds newSeen hm stats ev with
            | (none, stats1) => (none, stats1)
            | (some inner, stats1) =>
              (some (Formula.scope [] (some s!"never_a_1({id})") inner), addStat stats1 2)

      | "neg" | "_neg" =>
        match ep.rargs.find? (fun arg => arg.1 == "ARG1") with
        | none => (none, stats)
        | some (_, handle) =>
          let innerPreds := hm.find? handle |>.getD []
          match processPredicates ep.label innerPreds newSeen hm stats ev with
          | (none, stats1) => (none, stats1)
          | (some inner, stats1) =>
            (some (Formula.scope [] (some "neg") inner), addStat stats1 2)

      | "temp_compound_name" =>
        match ep.rargs with
        | [("X1", x1), ("X2", x2), ("A", a), ("B", b)] =>
          let aPreds := hm.find? a |>.getD []
          dbg_trace ("Looking up handle " ++ toString a ++ " in handleMap; found preds: " ++ toString aPreds)
          let bPreds := hm.find? b |>.getD []
          dbg_trace ("Looking up handle " ++ toString b ++ " in handleMap; found preds: " ++ toString bPreds)
          match processPredicates ep.label aPreds newSeen hm stats ev with
          | (none, stats1) => (none, stats1)
          | (some aFormula, stats1) =>
            match processPredicates ep.label bPreds newSeen hm stats1 ev with
            | (none, stats2) => (none, stats2) 
            | (some bFormula, stats2) =>
              match ep.carg with
              | some name =>
                dbg_trace ("SCOPE: temp_compound at " ++ toString ep.label)
                dbg_trace ("  aFormula: " ++ toString aFormula)
                dbg_trace ("  bFormula: " ++ toString bFormula)
                let namedEP := EP.mk "named" none ep.label [("ARG0", x1)] (some name)
                let rstr := Formula.atom namedEP
                let substitutedBFormula := bFormula.substitute x2 x1
                let body := Formula.conj [rstr, substitutedBFormula]
                dbg_trace ("  constructed body: " ++ toString body)
                (some (Formula.scope [x1] (some "proper_q") body), addStat stats2 1)
              | none => (none, stats2)
        | _ => (none, stats)

      | p =>
        if lastTwoChars p == "_q" then
          dbg_trace s!"Processing quantifier predicate: {p}"
          match getOrderedQuantArgs ep.rargs with 
          | none => (none, stats)
          | some (arg0, rstr, body) =>
            dbg_trace s!"SCOPE: quantifier {p}\n  ARG0: {arg0}\n  RSTR: {rstr}\n  BODY: {body}"
            let rstrPreds := hm.find? rstr |>.getD []
            dbg_trace s!"Looking up RSTR handle {rstr} in handleMap; found preds: {rstrPreds}"
            let bodyPreds := hm.find? body |>.getD []
            dbg_trace s!"Looking up BODY handle {body} in handleMap; found preds: {bodyPreds}"
            dbg_trace s!"Creating scope with quant: {p}"
            match processPredicates ep.label rstrPreds newSeen hm stats ev with
            | (none, stats1) => (none, stats1)
            | (some rstrFormula, stats1) =>
              dbg_trace s!"  RSTR preds for {p}: {rstrPreds}"
              dbg_trace s!"  RSTR result: {rstrFormula}"
              match processPredicates ep.label bodyPreds newSeen hm stats1 ev with
              | (none, stats2) => (none, stats2)
              | (some bodyFormula, stats2) =>
                dbg_trace s!"  BODY preds for {p}: {bodyPreds}"
                dbg_trace s!"  BODY result: {bodyFormula}"
                dbg_trace s!"Building final scope for {p} with arg0 {arg0}"
                (some (Formula.scope [arg0] (some p) (Formula.conj [rstrFormula, bodyFormula])), addStat stats2 3)
        else
          (some (Formula.atom ep), stats)

end

end PWL.Transform.Scoping

export PWL.Transform.Scoping (processPredicates processEP EliminatedVars isVarEliminated Stats collectEliminatedVars EliminatedVars.empty)
