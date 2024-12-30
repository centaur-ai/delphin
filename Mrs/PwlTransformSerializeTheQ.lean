import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformSerializeBase
import Mrs.PwlTransformMinScoping_Core
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.Serialize

open MRS (EP Var)
open HOF (lastTwoChars)
open PWL.Transform.Serialize (makeIndent normalizePredicate)
open PWL.Transform.MinScoping (isRstrPredicate ScopedEP)

def extractRstrBody (f : Formula) : (List Formula × List Formula) :=
  dbg_trace s!"PWL: extractRstrBody input formula:\n{f}"
  match f with
  | Formula.conj fs =>
    dbg_trace s!"PWL: examining {fs.length} conjuncts"
    match fs.find? fun f => match f with
      | Formula.scope [] (some "rstr_guard") _ => true 
      | _ => false
      with
    | none =>
      dbg_trace "PWL: no RSTR guard found"
      ([], fs)
    | some (Formula.scope _ _ inner) =>
      dbg_trace s!"PWL: found guarded RSTR scope:\n{inner}"
      -- If we find an RSTR guard scope, everything inside it should be RSTR
      match inner with
      | Formula.atom ep =>
        dbg_trace s!"PWL: found atomic RSTR:\n{ep}"
        ([Formula.atom ep], fs.filter fun f => match f with
          | Formula.scope [] (some "rstr_guard") _ => false
          | _ => true)
      | Formula.conj innerFs =>
        dbg_trace s!"PWL: found compound RSTR:\n{innerFs}"
        (innerFs, fs.filter fun f => match f with
          | Formula.scope [] (some "rstr_guard") _ => false
          | _ => true)
      | _ => ([], fs)
    | _ => ([], fs)
  | _ => 
    dbg_trace s!"PWL: no conjunction found in:\n{f}"
    ([], [f])

def formatTheQ (vars : List Var) (inner : Formula) (ind : Nat) 
    (formatFn : Formula → Option Var → Nat → Bool → Bool → String) : String :=
  dbg_trace s!"PWL: formatTheQ starting:\n{inner}"
  let baseIndent := makeIndent ind
  let contentIndent := makeIndent (ind + 2)

  match vars.head? with
  | none => 
    dbg_trace "PWL: THE_Q no variables - unreachable!"
    unreachable!
  | some x =>
    dbg_trace s!"PWL: Set var={x} vars={vars}"
    
    -- Extract RSTR and BODY predicates
    let (rstrPreds, bodyPreds) := extractRstrBody inner 
    dbg_trace s!"PWL: partition result:\nRSTR={rstrPreds}\nBODY={bodyPreds}"
    
    -- Format RSTR predicates for set comprehension
    let rstrStr := match rstrPreds with
    | [] => 
      dbg_trace "PWL: RSTR predicates empty"
      ""
    | preds => 
      dbg_trace s!"PWL: formatting RSTR predicates:\n{preds}"
      let rstrConj := Formula.conj preds
      dbg_trace s!"PWL: RSTR conjunction:\n{rstrConj}"
      let result := formatFn rstrConj none (ind + 4) false false
      dbg_trace s!"PWL: RSTR formatted result:\n{result}"
      result
    
    -- Format BODY predicates
    let bodyStr := if bodyPreds.isEmpty 
      then ""
      else
        dbg_trace s!"PWL: formatting BODY predicates:\n{bodyPreds}"
        let result := "\n" ++ formatFn (Formula.conj bodyPreds) none (ind + 4) false false
        dbg_trace s!"PWL: BODY formatted result:\n{result}"
        result

    -- Build final PWL string
    let result := s!"{baseIndent}?[S]:(/* the_q */\n" ++
                 s!"{contentIndent}S=^[s]:(\n" ++
                 s!"{rstrStr}) &\n" ++
                 s!"{contentIndent}size(S)=1 &\n" ++
                 s!"{contentIndent}?[{x}]:(\n" ++
                 s!"{contentIndent}  S({x})" ++
                 (if bodyStr == "" then ")" else s!" &{bodyStr})")
    dbg_trace s!"PWL: Final THE_Q result:\n{result}"
    result

end PWL.Transform.Serialize

export PWL.Transform.Serialize (formatTheQ)
