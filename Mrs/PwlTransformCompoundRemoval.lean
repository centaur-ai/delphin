import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.CompoundRemoval

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

def isEventOrImplicit (v : Var) : Bool :=
  v.sort == 'e' || v.sort == 'i'

mutual 
  partial def removeCompoundFromFormula (f : Formula) : Formula :=
    match f with
    | Formula.atom ep =>
      if ep.predicate == "compound" || ep.predicate == "_compound" then
        -- Find the two x-type variables
        let xvars := ep.rargs.filter (fun arg => arg.2.sort == 'x')
        match xvars with
        | [(name1, x1), (name2, x2)] =>
          -- Convert compound into equality between x variables
          Formula.atom { ep with
            predicate := "=",
            rargs := [("ARG1", x1), ("ARG2", x2)],  -- Will render as (x1 = x2)
            carg := some "/* compound */" }
        | _ => Formula.atom ep
      else Formula.atom ep

    | Formula.conj fs =>
      let rec processFormulas (remaining : List Formula) (acc : List Formula) : List Formula :=
        match remaining with
        | [] => acc
        | f :: rest => 
          let processed := removeCompoundFromFormula f
          match processed with
          | Formula.conj [] => processFormulas rest acc  
          | _ => processFormulas rest (acc ++ [processed])

      let processed := processFormulas fs []
      match processed with
      | [] => Formula.conj []
      | [single] => single  
      | multiple => Formula.conj multiple

    | Formula.scope vars quant inner =>
      let innerProcessed := removeCompoundFromFormula inner
      
      -- Check if this scope contains a compound predicate 
      let hasCompound := match innerProcessed with
        | Formula.atom ep => 
          if ep.predicate == "=" && ep.carg == some "/* compound */" then true else false
        | Formula.conj fs =>
          fs.any fun f => match f with
            | Formula.atom ep => 
              if ep.predicate == "=" && ep.carg == some "/* compound */" then true else false 
            | _ => false
        | _ => false

      -- If scope contains a compound and has event variable, empty the variable list but keep scope
      if hasCompound && vars.length == 1 && vars.head!.sort == 'e' then
        Formula.scope [] quant innerProcessed
      else if innerProcessed.isEmptyConj then
        Formula.conj []
      else
        Formula.scope vars quant innerProcessed 

end

def simplifyCompounds (f : Formula) : Formula :=
  dbg_trace "\n============= Starting compound simplification ============="
  dbg_trace s!"Input formula: {f}"
  let result := removeCompoundFromFormula f
  dbg_trace s!"Output formula: {result}"
  dbg_trace "=== Finished compound simplification ==="
  result

end PWL.Transform.CompoundRemoval

export PWL.Transform.CompoundRemoval (simplifyCompounds)
