import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS
open InsertionSort
open PWL.Transform
open Lean (HashMap)
open BEq

partial def getPredicatesFromFormula (f : Formula) (level : Nat) : List EP :=
  let rec aux : List EP → Formula → List EP
  | acc, Formula.atom ep => ep :: acc
  | acc, Formula.conj fs => 
    fs.foldl aux acc
  | acc, Formula.scope _ _ inner => 
    aux acc inner

  aux [] f

partial def getFormulaScopes (f : Formula) (level : Nat) : List ScopeInfo :=
  let rec aux : List ScopeInfo → Formula → List ScopeInfo
  | acc, Formula.atom _ => acc
  | acc, Formula.conj fs =>
    fs.foldl aux acc
  | acc, Formula.scope vars (some pred) inner =>
    let normalized := if pred.startsWith "_" then pred.drop 1 else pred
    let scopeType := 
      if normalized == "every_q" then ScopeType.Universal 
      else if normalized == "the_q" || normalized == "def_explicit_q" then ScopeType.Definite
      else if normalized == "never_a_1" then ScopeType.NeverNeg
      else if normalized == "neg" then ScopeType.RegNeg
      else if normalized == "colon_p_namely" then ScopeType.ColonNamely
      else ScopeType.Indefinite
    let info : ScopeInfo := {
      predicate := normalized,
      boundVars := orderVarsForScoping vars.eraseDups,
      scopeType := scopeType,
      negVar := if vars.isEmpty then none else some vars.head! }
    aux (info :: acc) inner
  | acc, Formula.scope _ none inner =>
    aux acc inner

  aux [] f

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (getPredicatesFromFormula getFormulaScopes)
