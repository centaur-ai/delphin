import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformScopingCore
import Mrs.PwlTransformScoping
import Mrs.PwlTransformSerialize
import Mrs.PwlTransformNegationScopeRemoval
import Mrs.PwlTransformEqualityRemoval
import Mrs.PwlTransformCompoundRemoval
import Mrs.PwlTransformLambdaTracking 
import Mrs.PwlTransformWhichQ
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform

open MRS (Var EP Constraint MRS)
open MM (Multimap)
open InsertionSort
open PWL.Transform.ScopingCore (EliminatedVars isVarEliminated collectEliminatedVars shouldEliminateHandle)
open PWL.Transform.Scoping (processPredicates)
open PWL.Transform.MinScoping (ScopedEP analyzeFormula)

structure RewriteConfig where
  rewriteAQ : Bool := false
  deriving Inhabited

def rewriteDefaultConfig : RewriteConfig :=
  { rewriteAQ := true }

instance : Ord (EP × Nat) where
  compare := fun p1 p2 => 
    match compare p1.2 p2.2 with
    | .eq => .eq
    | ord => ord

structure CompoundInfo where
  var1 : Var
  var2 : Var
  string1 : String
  string2 : String
  deriving Inhabited

def makeCompoundInfo (parent : Var) (ev : EliminatedVars) (pat : CompoundMatch) : Option CompoundInfo :=
  match pat.named1.predicate.carg, pat.named2.predicate.carg with 
  | some s1, some s2 =>
    match pat.properQ1.predicate.rargs.find? (fun arg => arg.1 == "ARG0"),
          pat.properQ2.predicate.rargs.find? (fun arg => arg.1 == "ARG0") with
    | some (_, var1), some (_, var2) =>
      some ⟨var1, var2, s1, s2⟩
    | _, _ => none
  | _, _ => none

def getReferencedHandles (compoundInfos : List CompoundInfo) : List Var :=
  compoundInfos.foldl (fun acc info => [info.var1, info.var2] ++ acc) []

def isCompoundInvolving (parent : Var) (pat : CompoundMatch) : Bool :=
  let isParentLabel := pat.properQ1.predicate.label == parent || pat.properQ2.predicate.label == parent
  let isParentBody := 
    (match pat.properQ1.predicate.rargs.find? (fun arg => arg.1 == "BODY") with
    | some (_, body) => body == parent
    | none => false) ||
    (match pat.properQ2.predicate.rargs.find? (fun arg => arg.1 == "BODY") with
    | some (_, body) => body == parent
    | none => false)
  isParentLabel || isParentBody

def updateHandleMap (preds : List EP) : Multimap Var EP :=
  let initial := preds.foldl (fun hm ep => hm.insert ep.label ep) Multimap.empty
  dbg_trace s!"updateHandleMap: Full handle map {if preds.length == initial.keys.length then "before" else "after"} phase1: {(initial.keys.map (fun h => h.sort.toString ++ toString h.id))}"
  initial

def phase0 (preds : List EP) : List EP :=
  let removeEventAnd (ep : EP) : Bool :=
    if ep.predicate == "and_c" || ep.predicate == "_and_c" then
      ep.rargs.all (fun arg => arg.2.sort == 'e')
    else
      false
  preds.filter (fun ep => !removeEventAnd ep)

partial def phase1 (parent : Var) (preds : List EP) (hm : Multimap Var EP) (dm : DepthMap) 
    : (List EP × List CompoundInfo × EliminatedVars × Var) :=
  let rec processCompounds (curPreds : List EP) (processedCompounds : List EP) 
      (compoundInfos : List CompoundInfo) (curRoot : Var) 
      : (List EP × List CompoundInfo × Var) := 
    -- Find unprocessed compounds
    let compounds := curPreds.filter fun p =>
      (p.predicate == "compound" || p.predicate == "_compound") &&
      !processedCompounds.any (fun c => c.label == p.label)
    
    dbg_trace s!"PHASE1 processing compounds iteration:"
    dbg_trace s!"  Current root: {curRoot}"
    dbg_trace s!"  Remaining unprocessed compounds: {compounds.map (fun p => s!"\n    ({p.predicate}, {p.label})")}"

    if compounds.isEmpty then
      dbg_trace "PHASE1 no more compounds found"
      (curPreds, compoundInfos, curRoot)
    else
      -- Get compound depths and sort
      let compoundDepths := compounds.map fun c =>
        let depth := match dm.depths.find? c.label with
                    | some d => d
                    | none => MAX_DEPTH
        (c, depth)
      
      let firstCompound := (insertionSort compoundDepths).head!.1
      dbg_trace s!"PHASE1 processing deepest compound: ({firstCompound.predicate}, {firstCompound.label})"

      match getCompoundPattern curPreds firstCompound hm dm with
      | none => 
        dbg_trace s!"PHASE1 pattern match failed for {firstCompound.label}, marking as processed"
        processCompounds curPreds (firstCompound :: processedCompounds) compoundInfos curRoot
      | some pat =>
        dbg_trace s!"PHASE1 pattern matched for {firstCompound.label}"
        dbg_trace s!"PHASE1 pattern details:"
        dbg_trace s!"  Compound: {pat.compound.predicate} ({pat.compound.label})"
        dbg_trace s!"  ProperQ1: {pat.properQ1.predicate.predicate} ({pat.properQ1.predicate.label})"
        dbg_trace s!"  ProperQ2: {pat.properQ2.predicate.predicate} ({pat.properQ2.predicate.label})"
        dbg_trace s!"  Named1: {pat.named1.predicate.predicate} ({pat.named1.predicate.label})"
        dbg_trace s!"  Named2: {pat.named2.predicate.predicate} ({pat.named2.predicate.label})"
        
        match makeCompoundInfo parent EliminatedVars.empty pat with 
        | none => 
          dbg_trace "PHASE1 info creation failed"
          processCompounds curPreds (firstCompound :: processedCompounds) compoundInfos curRoot
        | some info =>
          dbg_trace s!"PHASE1 created compound info for {firstCompound.label}"
          dbg_trace s!"  Var1: {info.var1}"
          dbg_trace s!"  Var2: {info.var2}"
          dbg_trace s!"  String1: {info.string1}"
          dbg_trace s!"  String2: {info.string2}"

          -- Update predicates
          let newPreds := curPreds.map fun p =>
            if p == pat.named2.predicate then
              -- Replace second named predicate with equality
              EP.mk "=" none pat.compound.label [("ARG1", info.var2), ("ARG2", info.var1)] none
            else if p == pat.named1.predicate then
              -- Update first named predicate with concatenated string
              {p with carg := some ("\"" ++ removeExtraQuotes info.string1 ++ " " ++ 
                                         removeExtraQuotes info.string2 ++ "\"")}
            else p

          -- Remove only this specific compound
          let filteredPreds := newPreds.filter fun p => !(p == pat.compound)
          
          let newRoot := if curRoot == pat.compound.label then pat.properQ1.predicate.label else curRoot
          dbg_trace s!"PHASE1 root update: {curRoot} -> {newRoot}"
          dbg_trace s!"PHASE1 updated predicates:"
          dbg_trace s!"  {filteredPreds.map (fun p => s!"\n    {p.predicate} ({p.label})")}"
          
          processCompounds filteredPreds 
            (firstCompound :: processedCompounds)
            (info :: compoundInfos)
            newRoot

  let (finalPreds, compoundInfos, finalRoot) := processCompounds preds [] [] parent
  let eliminatedVars := collectEliminatedVars finalPreds
  
  dbg_trace s!"PHASE1 complete:"
  dbg_trace s!"  Final root: {finalRoot}"
  dbg_trace s!"  All compound infos collected: {compoundInfos.map (fun info => 
    s!"\n    Var1: {info.var1}, Var2: {info.var2}, String1: {info.string1}, String2: {info.string2}")}"
  dbg_trace s!"  Final predicates: {finalPreds.map (fun p => s!"\n    ({p.predicate}, {p.label})")}"
  
  (finalPreds, compoundInfos, eliminatedVars, finalRoot)

def phase2 (parent : Var) (handle : Var) (preds : List EP) (ev : EliminatedVars) (hm : Multimap Var EP) : Option Formula :=
  dbg_trace s!"PHASE2: Initial state: parent={parent} handle={handle}\nAll predicates:\n{preds.map (fun p => 
    (p.predicate, p.label, p.rargs.map (fun a => (a.1, a.2)), p.carg))}"

  match hm.find? handle with 
  | none => 
    dbg_trace s!"PHASE2: No predicates found for handle {handle}"
    none
  | some rootPreds => 
    dbg_trace s!"PHASE2: Root predicates for {handle}:\n{rootPreds.map (fun p => 
      (p.predicate, p.label, p.rargs.map (fun a => (a.1, a.2)), p.carg))}"
    dbg_trace s!"PHASE2: Processing with:\n  Parent={parent}\n  Handle={handle}\n  EliminatedVars={ev.vars}"
    
    match processPredicates handle rootPreds [] hm default ev with
    | (some formula, _) => 
      dbg_trace s!"PHASE2: Generated formula: {formula}"
      some formula
    | (none, _) => 
      dbg_trace s!"PHASE2: Failed to generate formula"
      none

def phase3 := PWL.Transform.NegationScopeRemoval.simplifyNegation

def phase3_1_with_debug (f : Formula) : Formula := 
  dbg_trace "\n=== STARTING EQUALITY SIMPLIFICATION (PHASE 3.1) ==="
  dbg_trace s!"Input formula: {f}"
  let result := PWL.Transform.EqualityRemoval.simplifyEqualities f
  dbg_trace s!"Output formula: {result}"
  dbg_trace "=== FINISHED EQUALITY SIMPLIFICATION ==="
  result

def phase3_2 := PWL.Transform.CompoundRemoval.simplifyCompounds

def phase3_3 : Formula → (Formula × Lean.RBTree Var compare) :=
  PWL.Transform.LambdaTracking.simplifyLambdas

def phase3_4 := PWL.Transform.WhichQ.simplifyWhichQ

partial def rewriteAQ (f : Formula) (cfg : RewriteConfig := rewriteDefaultConfig) : Formula :=
  if !cfg.rewriteAQ then f
  else
    let rec rewrite (f : Formula) : Formula :=
      match f with 
      | Formula.scope vars (some q) inner =>
        let newQuant := if q == "a_q" || q == "_a_q" 
                       then "every_q" 
                       else q
        Formula.scope vars (some newQuant) (rewrite inner)
      | Formula.scope vars none inner =>
        Formula.scope vars none (rewrite inner)
      | Formula.conj fs =>
        Formula.conj (fs.map rewrite)
      | Formula.atom ep => Formula.atom ep
    rewrite f

def phase3_5 (f : Formula) (cfg : RewriteConfig := rewriteDefaultConfig) : Formula := 
  dbg_trace "\n============= Starting a_q rewrite ============="
  dbg_trace s!"Input formula: {f}"
  let result := rewriteAQ f cfg
  dbg_trace s!"Output formula: {result}"
  dbg_trace "=== Finished a_q rewrite ==="
  result

def phase4 (f : Formula) (lambdaVars : Lean.RBTree Var compare) : String :=
  formatAsPWL f lambdaVars none

def transform (handle : Var) (preds : List EP) (hm : Multimap Var EP) : String :=
  dbg_trace s!"Transform - Starting with handle {handle}\nPreds count: {preds.length}\nHandle map size: {hm.keys.length}\nHandle map contents: {(hm.keys.map fun k => (k, hm.find? k))}"

  let filteredPreds := phase0 preds
  dbg_trace s!"POST_PHASE0: After phase0 filtered predicates: {filteredPreds.map (fun p => (p.predicate, p.label))}"
  
  let dm := computeDepthMap handle hm
  let (p1preds, compoundInfos, ev, newRoot) := phase1 handle filteredPreds hm dm
  dbg_trace s!"POST_PHASE1: Preds from phase1: {p1preds.map (fun p => (p.predicate, p.label))}"
  dbg_trace s!"POST_PHASE1: New root={newRoot} eliminatedVars={ev.vars}"
  dbg_trace s!"POST_PHASE1: Compound infos: {compoundInfos.map (fun info => (info.var1, info.var2))}"
  
  dbg_trace "POST_PHASE1: Updating handle map with phase1 results" 
  let newHm := updateHandleMap p1preds
  dbg_trace s!"POST_PHASE1: Updated handle map keys: {newHm.keys}"

  match phase2 handle newRoot p1preds ev newHm with
  | none => 
    dbg_trace "POST_PHASE2: No formula generated"
    "!!! NO FORMULA GENERATED !!!"
  | some formula =>
      dbg_trace s!"POST_PHASE2: Generated formula: {formula}"
      let negSimplified := phase3 formula
      dbg_trace s!"POST_PHASE3: Negation simplified: {negSimplified}"
      let equalitySimplified := phase3_1_with_debug negSimplified
      dbg_trace s!"POST_PHASE3.1: Equality simplified: {equalitySimplified}"
      let compoundSimplified := phase3_2 equalitySimplified 
      dbg_trace s!"POST_PHASE3.2: Compound simplified: {compoundSimplified}"
      let (preFormat, lambdaVars) := phase3_3 compoundSimplified
      dbg_trace s!"POST_PHASE3.3: Lambda variables collected: {lambdaVars.fold (init := []) fun xs x => x :: xs}"
      let whichQSimplified := phase3_4 preFormat
      dbg_trace s!"POST_PHASE3.4: Which-Q simplified: {whichQSimplified}"
      let aqRewritten := phase3_5 whichQSimplified rewriteDefaultConfig
      dbg_trace s!"POST_PHASE3.5: A_Q rewritten: {aqRewritten}"
      let result := phase4 aqRewritten lambdaVars
      dbg_trace s!"Final result: {result}"
      result

end PWL.Transform

export PWL.Transform (transform)
