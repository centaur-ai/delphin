import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.Hof
import Util.InsertionSort
import Lean.Data.RBTree

namespace PWL.Transform.WhichQ

open MRS (Var EP)
open InsertionSort
open PWL.Transform

def isLambdaVar (v : Var) : Bool :=
  let result := v.sort == 'q' && v.id == 0
  dbg_trace s!"isLambdaVar: var={v} sort={v.sort} id={v.id} result={result}"
  result

partial def transformWhichQ (f : Formula) : Formula :=
  dbg_trace s!"WHICH_Q: processing formula:\n{f}"
  
  let rec findWhichQVar : Formula → Option Var
    | Formula.atom _ => 
      dbg_trace "WHICH_Q: found atom"
      none 
    | Formula.scope vars (some q) inner => 
      dbg_trace s!"WHICH_Q: examining scope with quantifier {q} and vars {vars}"
      if q.endsWith "which_q" then 
        match vars with
        | [] => none
        | v::_ => 
          dbg_trace s!"WHICH_Q: found which_q variable {v}"
          some v
      else
        dbg_trace "WHICH_Q: recursing into inner scope"
        findWhichQVar inner
    | Formula.scope _ none inner => 
      dbg_trace "WHICH_Q: recursing through scopeless formula" 
      findWhichQVar inner
    | Formula.conj fs =>
      dbg_trace s!"WHICH_Q: examining conjunction with {fs.length} parts"
      fs.foldl (fun acc f => match acc with 
        | some v => some v
        | none => findWhichQVar f) none

  let rec addEqual (whichVar : Var) : Formula → Formula
    | Formula.scope vars (some q) inner =>
      dbg_trace s!"WHICH_Q: adding equality at scope {q}"
      if q.endsWith "which_q" then
        dbg_trace s!"WHICH_Q: adding q0 = {whichVar} to which_q scope"
        Formula.scope vars (some q) $
          Formula.conj [inner, Formula.atom {
            predicate := "=",
            link := none,
            label := whichVar,
            rargs := [("ARG1", ⟨0, 'q', #[]⟩), ("ARG2", whichVar)],
            carg := none
          }]
      else Formula.scope vars (some q) (addEqual whichVar inner)
    | Formula.scope vars none inner =>
      Formula.scope vars none (addEqual whichVar inner)
    | Formula.conj fs =>
      Formula.conj (fs.map (addEqual whichVar))
    | f => f

  match findWhichQVar f with
  | none => 
    dbg_trace "WHICH_Q: no which_q found"
    f
  | some whichVar =>
    dbg_trace s!"WHICH_Q: wrapping formula with ^[q0]: for variable {whichVar}"
    Formula.scope [⟨0, 'q', #[]⟩] none $
      addEqual whichVar f

def simplifyWhichQ (f : Formula) : Formula :=
  dbg_trace "\n============= Starting which-q transformation ============="
  let result := transformWhichQ f
  dbg_trace s!"Output formula: {result}"
  dbg_trace "=== Finished which-q transformation ==="
  result

end PWL.Transform.WhichQ

export PWL.Transform.WhichQ (simplifyWhichQ isLambdaVar)
