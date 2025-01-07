import Mrs.Basic
import Mrs.PwlTypes 
import Mrs.PwlTransformShared
import Mrs.Hof
import Util.InsertionSort
import Lean.Data.RBTree
import Lean.Data.RBMap

namespace PWL.Transform.LambdaTracking

open MRS (Var EP)
open InsertionSort
open PWL.Transform
open Lean

def isConjunction (ep : EP) : Bool :=
  ep.predicate == "and_c" || ep.predicate == "_and_c" ||
  ep.predicate == "implicit_conj" || ep.predicate == "_implicit_conj"

mutual 
  partial def collectLambdas (f : Formula) : (Formula × RBTree Var compare) :=
    match f with
    | Formula.atom ep =>
      if isConjunction ep then
        match ep.rargs.find? (fun arg => arg.1 == "ARG0") with 
        | some (_, x) => (f, RBTree.empty.insert x)  -- x is ARG0/lambda output
        | none => (f, RBTree.empty)
      else 
        (f, RBTree.empty)

    | Formula.conj fs =>
      let (newFs, sets) := fs.foldl 
        (fun (acc, set) f =>
          let (newF, newSet) := collectLambdas f
          (acc ++ [newF], set.fold (init := newSet) fun s x => s.insert x))
        ([], RBTree.empty)
      (Formula.conj newFs, sets)

    | Formula.scope vars quant inner =>
      let (newInner, set) := collectLambdas inner 
      (Formula.scope vars quant newInner, set)
end

def simplifyLambdas (f : Formula) : (Formula × RBTree Var compare) := 
  dbg_trace "\n============= Starting lambda collection ============="
  dbg_trace s!"Input formula: {f}"
  let result := collectLambdas f
  dbg_trace s!"Output formula: {result.1}"
  dbg_trace s!"Lambda variables: {result.2.fold (init := []) fun xs x => x :: xs}"
  dbg_trace "=== Finished lambda collection ==="
  result

end PWL.Transform.LambdaTracking

export PWL.Transform.LambdaTracking (simplifyLambdas)
