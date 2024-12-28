import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared

namespace PWL.Transform.NegationScopeRemoval

open MRS (Var EP)

-- Helper function to check if an event or implicit variable is used in a formula
partial def isEventOrImplicitVarUsed (var : Var) (f : Formula) : Bool :=
  match f with
  | Formula.atom ep =>
    ep.rargs.any (fun arg => arg.2 == var)
  | Formula.conj formulas =>
    formulas.any (isEventOrImplicitVarUsed var)
  | Formula.scope vars _ inner =>
    if vars.contains var then false
    else isEventOrImplicitVarUsed var inner

-- Helper to determine if a variable is an event or implicit type
def isEventOrImplicitVar (var : Var) : Bool :=
  var.sort == 'e' || var.sort == 'i'

-- Recursive helper to process negation scopes
partial def simplifyNegationHelper (f : Formula) : Formula :=
  match f with
  | Formula.atom ep => Formula.atom ep
  | Formula.conj formulas => 
    Formula.conj (formulas.map simplifyNegationHelper)
  | Formula.scope vars quant inner =>
    match quant with
    | some q =>
      if q == "neg" || q == "_neg" || q == "never_a_1" || q == "_never_a_1" then
        -- Check if event/implicit variable is actually used in inner formula
        match vars.find? isEventOrImplicitVar with
        | none => Formula.scope vars quant (simplifyNegationHelper inner)
        | some var =>
          if isEventOrImplicitVarUsed var inner then
            Formula.scope vars quant (simplifyNegationHelper inner)
          else
            -- Remove scope but preserve negation
            Formula.scope [] quant (simplifyNegationHelper inner)
      else
        Formula.scope vars quant (simplifyNegationHelper inner)
    | none => Formula.scope vars none (simplifyNegationHelper inner)

def simplifyNegation (f : Formula) : Formula := 
  dbg_trace "Phase 5 - Simplifying negation scopes"
  simplifyNegationHelper f

end PWL.Transform.NegationScopeRemoval

export PWL.Transform.NegationScopeRemoval (simplifyNegation)
