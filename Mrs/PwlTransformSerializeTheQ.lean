import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformSerializeBase
import Mrs.Hof

namespace PWL.Transform.Serialize

open MRS (EP Var)
open HOF (lastTwoChars)
open PWL.Transform.Serialize (makeIndent normalizePredicate)

def formatTheQ (vars : List Var) (inner : Formula) (ind : Nat)
    (formatFn : Formula → Option Var → Nat → Bool → Bool → String) : String :=
  dbg_trace s!"THE_Q[{ind}] starting\n  vars: {vars}\n  inner: {inner}"
  let baseIndent := makeIndent ind
  let contentIndent := makeIndent (ind + 2)
  let innerIndent := makeIndent (ind + 4)

  dbg_trace s!"THE_Q[{ind}] indents\n  base: '{baseIndent}'\n  content: '{contentIndent}'\n  inner: '{innerIndent}'"

  match vars.head? with
  | none => 
    dbg_trace "THE_Q no variables - unreachable!"
    unreachable!
  | some x =>
    dbg_trace s!"THE_Q[{ind}] processing with var: {x}"
    let formattedInner := formatFn inner none (ind + 4) false false
    -- Added closing parenthesis after S({x})
    s!"{baseIndent}?[S]:(/* the_q */\n{contentIndent}S=^[s]:(\n{formattedInner}) &\n{contentIndent}size(S)=1 &\n{contentIndent}?[{x}]:(\n{contentIndent}  S({x})))"

end PWL.Transform.Serialize

export PWL.Transform.Serialize (formatTheQ)
