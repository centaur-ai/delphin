import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.Scoping

open MRS (EP Var)
open MM (Multimap)
open PWL.Transform (Formula Stats addStat)
open HOF (lastTwoChars)
open InsertionSort
open BEq

structure EliminatedVars where
  vars : List Var
  deriving Inhabited

def EliminatedVars.empty : EliminatedVars := 
  EliminatedVars.mk []

def orderPredicateArgs (args : List (String × Var)) : List (String × Var) :=
  args.filter (fun a => a.1.startsWith "ARG") |> insertionSort

def isVarEliminated (ev : EliminatedVars) (v : Var) : Bool :=
  dbg_trace s!"isVarEliminated checking {v} against list {ev.vars}"
  ev.vars.contains v

def shouldEliminateHandle (hm : Multimap Var EP) (ev : EliminatedVars) (handle : Var) : Bool :=
  match hm.find? handle with
  | none => unreachable!  
  | some eps =>
    dbg_trace s!"shouldEliminateHandle checking handle {handle}"
    eps.any fun ep =>
      dbg_trace s!"  checking EP {ep}"
      ep.rargs.any fun (_, v) => 
        let isElim := isVarEliminated ev v
        dbg_trace s!"    arg {v} eliminated? {isElim}"
        isElim

def collectEliminatedVars (preds : List EP) : EliminatedVars :=
  dbg_trace "collectEliminatedVars starting"
  dbg_trace s!"Input predicates: {preds}"
  let result := preds.foldl (fun acc ep =>
    dbg_trace s!"Checking predicate: {ep.predicate}"
    dbg_trace s!"  lastTwoChars: {lastTwoChars ep.predicate}"
    dbg_trace s!"  args: {ep.rargs}"
    if lastTwoChars ep.predicate == "_q" then
      match ep.rargs with
      | ("ARG0", v) :: _ => 
        dbg_trace s!"  found quantifier {ep.predicate}, adding {v}"
        EliminatedVars.mk (v :: acc.vars)
      | other => 
        dbg_trace s!"  quantifier {ep.predicate} has unexpected args: {other}"
        acc
    else acc
  ) EliminatedVars.empty
  dbg_trace s!"collectEliminatedVars complete with {result.vars}"
  result

def getScopableArgs (ep : EP) : List (String × Var) :=
  ep.rargs.filter (fun arg => arg.2.sort == 'x' || arg.2.sort == 'e' || arg.2.sort == 'i')

mutual 
  partial def processPredicates (parent : Var) (eps : List EP) (seenHandles : List Var) 
      (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
    dbg_trace ("processPredicates entry:")
    dbg_trace ("  parent handle: " ++ toString parent)
    dbg_trace ("  predicates to process: " ++ toString eps)
    dbg_trace ("  seen handles: " ++ toString seenHandles)
    dbg_trace ("  eliminated vars: " ++ toString ev.vars)
    
    let handleRefs := eps.foldl (fun acc ep => 
      ep.rargs.foldl (fun acc2 (name, v) => 
        if v.sort == 'h' then (ep.label, name, v) :: acc2 else acc2) acc) []
    dbg_trace ("  handle references found: " ++ toString handleRefs)
    
    (match eps with
    | [] => (some (Formula.conj []), stats)
    | [ep] => processEP parent ep seenHandles hm stats ev
    | eps =>
      dbg_trace ("processPredicates for handle " ++ toString parent)
      dbg_trace ("  predicates: " ++ toString eps)
      dbg_trace ("  handleMap keys: " ++ toString hm.keys)
      (match processEPs parent eps seenHandles hm stats ev with
      | (formulas, finalStats) =>
        dbg_trace ("  results: " ++ toString formulas)
        (match formulas with
        | [] => (some (Formula.conj []), finalStats)
        | fs => (some (Formula.conj fs), finalStats))))

  partial def processEPs (parent : Var) (eps : List EP) (seenHandles : List Var)
      (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (List Formula × Stats) :=
    eps.foldl (fun (acc, stats) ep =>
      match processEP parent ep seenHandles hm stats ev with
      | (some formula, newStats) => (acc ++ [formula], newStats)
      | (none, newStats) => (acc, newStats)) ([], stats)

  partial def isSimpleNamed (f : Formula) : Bool :=
    match f with 
    | Formula.atom ep => ep.predicate == "named" || ep.predicate == "_named"
    | _ => false

  partial def processEP (parent : Var) (ep : EP) (seenHandles : List Var)
      (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
    dbg_trace ("processEP starting with:")
    dbg_trace ("  parent: " ++ toString parent)
    dbg_trace ("  ep: " ++ toString ep)
    dbg_trace ("  seen handles: " ++ toString seenHandles)
    dbg_trace ("  eliminated vars: " ++ toString ev.vars)
    
    (if seenHandles.contains ep.label || shouldEliminateHandle hm ev ep.label then
      dbg_trace "  skipping due to seen/eliminated handle"
      (none, stats)
    else
      let newSeen := ep.label :: seenHandles
      (match ep.predicate with
      | "neg" | "_neg" | "never_a_1" | "_never_a_1" =>
        dbg_trace "Processing negation predicate"
        dbg_trace ("  at handle: " ++ toString ep.label)
        dbg_trace ("  with args: " ++ toString ep.rargs)
        dbg_trace ("  parent handle: " ++ toString parent)
        dbg_trace ("  seen handles: " ++ toString seenHandles)
        (match ep.rargs.find? (fun arg => arg.1 == "ARG1"), ep.rargs.find? (fun arg => arg.1 == "ARG0") with
        | some (_, handle), some (_, evar) =>
          dbg_trace ("  neg handle arg: " ++ toString handle)
          dbg_trace ("  neg event arg: " ++ toString evar)
          let innerPreds := hm.find? handle |>.getD []
          dbg_trace ("  inner preds for negation: " ++ toString innerPreds)
          (match processPredicates ep.label innerPreds newSeen hm stats ev with
          | (none, stats1) => 
            dbg_trace "  negation inner processing returned none"
            (none, stats1)
          | (some inner, stats1) =>
            dbg_trace ("  negation inner formula: " ++ toString inner)
            (some (Formula.scope [evar] (some ep.predicate) inner), addStat stats1 2))
        | _, _ => 
          dbg_trace "Missing required args for negation"
          (none, stats))
      
      | "colon_p_namely" | "_colon_p_namely" =>
        dbg_trace "Processing colon_p_namely predicate"
        dbg_trace s!"  at handle: {ep.label}"
        dbg_trace s!"  with args: {ep.rargs}"
        match ep.rargs.find? (fun arg => arg.1 == "ARG0"), 
              ep.rargs.find? (fun arg => arg.1 == "ARG1"), 
              ep.rargs.find? (fun arg => arg.1 == "ARG2") with
        | some (_, evar), some (_, handle1), some (_, handle2) =>
          dbg_trace s!"  event arg: {evar}"
          dbg_trace s!"  first handle: {handle1}"
          dbg_trace s!"  second handle: {handle2}"
          let innerPreds1 := hm.find? handle1 |>.getD []
          let innerPreds2 := hm.find? handle2 |>.getD []
          dbg_trace s!"  first preds: {innerPreds1}"
          dbg_trace s!"  second preds: {innerPreds2}"
          match processPredicates handle1 innerPreds1 newSeen hm stats ev with
          | (none, stats1) => 
            dbg_trace "  first handle processing returned none"
            (none, stats1)
          | (some part1, stats1) =>
            match processPredicates handle2 innerPreds2 newSeen hm stats1 ev with
            | (none, stats2) =>
              dbg_trace "  second handle processing returned none" 
              (none, stats2)
            | (some part2, stats2) =>
              dbg_trace s!"  part1: {part1}"
              dbg_trace s!"  part2: {part2}"
              (some (Formula.scope [evar] (some ep.predicate) (Formula.conj [part1, part2])), addStat stats2 4)
        | _, _, _ => 
          dbg_trace "  missing required arguments"
          (none, stats)

      | "temp_compound_name" =>
        dbg_trace s!"processEP: temp_compound_name with label {ep.label}"
        (match ep.rargs with
        | [("X1", x1), ("X2", x2), ("A", a), ("B", b)] =>
          let aPreds := hm.find? a |>.getD []
          dbg_trace ("Looking up handle " ++ toString a ++ " in handleMap; found preds: " ++ toString aPreds)
          let bPreds := hm.find? b |>.getD []
          dbg_trace ("Looking up handle " ++ toString b ++ " in handleMap; found preds: " ++ toString bPreds)
          (match processPredicates ep.label aPreds newSeen hm stats ev with
          | (none, stats1) => 
            dbg_trace "  a handle processing returned none"
            (none, stats1)
          | (some aFormula, stats1) =>
            dbg_trace s!"  a handle returned formula: {aFormula}"
            (match processPredicates ep.label bPreds newSeen hm stats1 ev with
            | (none, stats2) => 
              dbg_trace "  b handle processing returned none"
              (none, stats2) 
            | (some bFormula, stats2) =>
              dbg_trace s!"  b handle returned formula: {bFormula}"
              (match ep.carg with
              | some name =>
                dbg_trace ("SCOPE: temp_compound at " ++ toString ep.label)
                dbg_trace ("  aFormula: " ++ toString aFormula)
                dbg_trace ("  bFormula: " ++ toString bFormula)
                let namedEP := EP.mk "named" none ep.label [("ARG0", x1)] (some name)
                let rstr := Formula.atom namedEP
                let substitutedAFormula := if isSimpleNamed aFormula then
                  Formula.conj []  -- Skip simple named predicate
                else 
                  aFormula.substitute x2 x1
                let substitutedBFormula := bFormula.substitute x2 x1
                let body := Formula.conj [rstr, substitutedAFormula, substitutedBFormula]
                dbg_trace ("  constructed body: " ++ toString body)
                (some (Formula.scope [x1] (some "proper_q") body), addStat stats2 1)
              | none => 
                dbg_trace "  temp_compound missing CARG"
                (none, stats2))))
        | _ => 
          dbg_trace "Invalid temp_compound_name args"
          (none, stats))

      | p =>
        (if lastTwoChars p == "_q" then
          dbg_trace s!"Found quantifier predicate: {p}"
          dbg_trace "  RSTR and BODY handles to process"
          (match getOrderedQuantArgs ep.rargs with
          | none => 
            dbg_trace "  Could not get quantifier args!"
            (none, stats)
          | some (arg0, rstr, body) =>
            dbg_trace s!"  ARG0: {arg0}"
            dbg_trace s!"  RSTR: {rstr} with predicates: {hm.find? rstr}"
            dbg_trace s!"  BODY: {body} with predicates: {hm.find? body}"
            let rstrPreds := hm.find? rstr |>.getD []
            dbg_trace s!"Looking up RSTR handle {rstr} in handleMap; found preds: {rstrPreds}"
            let bodyPreds := hm.find? body |>.getD []
            dbg_trace s!"Looking up BODY handle {body} in handleMap; found preds: {bodyPreds}"
            (match processPredicates ep.label rstrPreds newSeen hm stats ev with
            | (none, stats1) => (none, stats1)
            | (some rstrFormula, stats1) =>
              dbg_trace s!"  RSTR preds for {p}: {rstrPreds}"
              dbg_trace s!"  RSTR result: {rstrFormula}"
              (match processPredicates ep.label bodyPreds newSeen hm stats1 ev with
              | (none, stats2) => (none, stats2)
              | (some bodyFormula, stats2) =>
                dbg_trace s!"  BODY preds for {p}: {bodyPreds}"
                dbg_trace s!"  BODY result: {bodyFormula}"
                dbg_trace s!"Building final scope for {p} with arg0 {arg0}"
                (some (Formula.scope [arg0] (some p) (Formula.conj [rstrFormula, bodyFormula])), addStat stats2 3))))
        else 
          dbg_trace "Processing non-quantifier predicate"
          (some (Formula.atom ep), stats))))
end

end PWL.Transform.Scoping

