import Mrs.Basic
import Mrs.PwlTypes 
import Mrs.PwlTransformScoping
import Mrs.PwlTransformShared 
import Mrs.PwlTransformMinScoping
import Mrs.PwlTransformSerialize
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform

open MRS (Var EP Constraint MRS)
open MM (Multimap)
open Lean (Format HashMap)
open InsertionSort
open HOF (lastTwoChars)
open PWL.Transform.Scoping (EliminatedVars isVarEliminated collectEliminatedVars shouldEliminateHandle)

def makeTemp (parent : Var) (ev : EliminatedVars) (pat : CompoundMatch) : Option EP :=
  dbg_trace ("Making temp_compound_name with: " ++
             "pat.properQ1=" ++ toString pat.properQ1 ++
             " pat.properQ2=" ++ toString pat.properQ2 ++
             " pat.named1=" ++ toString pat.named1 ++
             " pat.named2=" ++ toString pat.named2)

  (match pat.named1.carg, pat.named2.carg with
  | some s1, some s2 =>
    let x1 := pat.properQ1.rargs.find? (fun arg => arg.1 == "ARG0")
    let x2 := pat.properQ2.rargs.find? (fun arg => arg.1 == "ARG0")
    let b1 := pat.properQ1.rargs.find? (fun arg => arg.1 == "BODY")
    let b2 := pat.properQ2.rargs.find? (fun arg => arg.1 == "BODY") 
    match x1, x2, b1, b2 with
    | some (_, var1), some (_, var2), some (_, body1), some (_, body2) =>
      some (EP.mk "temp_compound_name" none parent
        [("X1", var1), ("X2", var2), ("A", body1), ("B", body2)]
        (some ("\"" ++ removeExtraQuotes s1 ++ " " ++ removeExtraQuotes s2 ++ "\"")))
    | _, _, _, _ => none
  | _, _ => none)

mutual
  partial def processPredicates (parent : Var) (eps : List EP) (seenHandles : List Var) 
      (hm : Multimap Var EP) (stats : Stats) (ev : EliminatedVars) : (Option Formula × Stats) :=
    match eps with
    | [] => (some (Formula.conj []), stats)
    | [ep] => processEP parent ep seenHandles hm stats ev
    | _ =>
      dbg_trace ("processPredicates for handle " ++ toString parent)
      dbg_trace ("  predicates: " ++ toString eps)
      dbg_trace ("  handleMap keys: " ++ toString hm.keys)
      match processEPs parent eps seenHandles hm stats ev with
      | (formulas, finalStats) =>
        dbg_trace ("  results: " ++ toString formulas)
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
    if seenHandles.contains ep.label || shouldEliminateHandle hm ev ep.label then
      (none, stats)
    else
      let newSeen := ep.label :: seenHandles
      dbg_trace s!"processEP: {ep.predicate} with label {ep.label}"
      match ep.predicate with 
      | "never_a_1" | "_never_a_1" =>
        match ep.rargs.find? (fun arg => arg.1 == "ARG1"), ep.rargs.find? (fun arg => arg.1 == "ARG0") with
        | some (_, handle), some (_, ivar) =>
          let innerPreds := hm.find? handle |>.getD []
          match processPredicates ep.label innerPreds newSeen hm stats ev with
          | (none, stats1) => (none, stats1)
          | (some inner, stats1) =>
            (some (Formula.neg (NegationType.Never ivar) inner), addStat stats1 2)
        | _, _ => (none, stats)

      | "neg" | "_neg" =>
        match ep.rargs.find? (fun arg => arg.1 == "ARG1") with
        | none => (none, stats)
        | some (_, handle) =>
          let innerPreds := hm.find? handle |>.getD []
          -- Get the event variable if it exists
          let evar := match ep.rargs.find? (fun arg => arg.1 == "ARG0") with
            | some (_, e) => e
            | none => {id := 0, sort := 'e', props := #[]}
          match processPredicates ep.label innerPreds newSeen hm stats ev with
          | (none, stats1) => (none, stats1)
          | (some inner, stats1) =>
            (some (Formula.neg (NegationType.NegWithEvent evar) inner), addStat stats1 2)

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

def phase1 (parent : Var) (preds : List EP) (hm : Multimap Var EP) : (List EP × EliminatedVars) :=
  let compounds := preds.filter fun p => 
    p.predicate == "compound" || p.predicate == "_compound"
  dbg_trace ("Found compounds: " ++ toString compounds)
  
  let patterns := compounds.filterMap (fun c => getCompoundPattern preds c hm)
  dbg_trace ("Found patterns: " ++ toString patterns)
  dbg_trace ("Found pattern handles: " ++ toString (patterns.map (fun p => p.compound.label)))

  let temps := patterns.filterMap (makeTemp parent EliminatedVars.empty)
  dbg_trace ("Created temp compounds: " ++ toString temps)

  let eliminatedVars := collectEliminatedVars $
    patterns.filter (fun p => temps.any (fun t => t.predicate == "temp_compound_name"))
    |>.map (fun p => p.compound)
  
  let remaining := preds.filter fun p =>
    not (patterns.any (shouldRemove p))
  
  dbg_trace ("Remaining predicates: " ++ toString remaining)
  
  (remaining ++ temps, eliminatedVars)

def phase2 (parent : Var) (handle : Var) (preds : List EP) (ev : EliminatedVars) (hm : Multimap Var EP) : Option Formula :=
  match hm.find? handle with 
  | none => unreachable!
  | some rootPreds => 
    dbg_trace ("phase2 starting at handle " ++ toString handle)
    dbg_trace ("  root predicates: " ++ toString rootPreds)
    let substitutions := preds.foldl (fun acc ep =>
      if ep.predicate == "temp_compound_name" then
        match (getArg ep "X1", getArg ep "X2") with
        | (some x1, some x2) => (x2, x1) :: acc
        | _ => acc
      else acc) []
    dbg_trace s!"Collected substitutions: {substitutions}"

    let emptyStats : Stats := default
    let (result, _) := processPredicates handle rootPreds [] hm emptyStats ev
    match result with
    | none => none
    | some formula =>
      some (substitutions.foldl (fun f (old, new) => f.substitute old new) formula)
      |>.map Formula.removeEmptyConj

def phase3 (f : Formula) : Formula :=
  minimizeScoping f

def phase4 (f : Formula) : String :=
  formatAsPWL f none

def updateHandleMap (preds : List EP) : Multimap Var EP :=
  preds.foldl (fun hm ep => hm.insert ep.label ep) Multimap.empty

def transform (handle : Var) (preds : List EP) (hm : Multimap Var EP) : String :=
  let msg := "Transform - Starting with handle " ++ toString handle ++
             "\nPreds count: " ++ toString preds.length ++
             "\nHandle map size: " ++ toString hm.keys.length
  dbg_trace msg
  
  let (p1preds, ev) := phase1 handle preds hm
  dbg_trace ("After phase1, updating handle map with temp compounds")
  let newHm := updateHandleMap p1preds 
  dbg_trace ("  new handle map size: " ++ toString newHm.keys.length)
  
  match phase2 handle handle p1preds ev newHm with
  | none => "!!! NO FORMULA GENERATED !!!"
  | some formula => 
      let minScoped := phase3 formula
      phase4 minScoped

end PWL.Transform

export PWL.Transform (transform)
