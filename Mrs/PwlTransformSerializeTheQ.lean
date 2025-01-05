import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Mrs.PwlTransformFormat
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform.Serialize

open MRS (Var EP)
open HOF (lastTwoChars)
open PWL.Transform

mutual 
  partial def substituteInFormula (f : Formula) (x : Var) (s : String) : Formula :=
    match f with
    | Formula.atom ep => 
      let newArgs := ep.rargs.map fun (name, var) =>
        if var == x then (name, {var with id := 0, sort := 's'}) else (name, var)
      Formula.atom { ep with rargs := newArgs }
    | Formula.conj fs => Formula.conj (fs.map (fun f => substituteInFormula f x s))
    | Formula.scope vars quant inner => Formula.scope vars quant (substituteInFormula inner x s)

  partial def extractFromGuard (f : Formula) : (List Formula × List Formula) :=
    dbg_trace s!"THE_Q_SERIALIZE: examining formula {match f with
      | Formula.conj fs => s!"conj({fs.length})"
      | Formula.scope vs q _ => s!"scope(vars={vs}, quant={q})" 
      | Formula.atom ep => s!"atom({ep.predicate})"}"

    match f with
    | Formula.conj fs =>
      let (rstrGuards, bodyFormulas) := fs.partition fun f => match f with
        | Formula.scope _ (some "rstr_guard") _ => true
        | _ => false 
      
      match rstrGuards with
      | [] => ([], fs)
      | guards => (guards, bodyFormulas)  -- Preserve complete guard formulas

    | Formula.scope [] (some "rstr_guard") inner =>
      ([Formula.scope [] (some "rstr_guard") inner], [])

    | other => ([], [other])
end

def formatTheQ (vars : List Var) (inner : Formula) (ind : Nat) 
    (formatFn : Formula → Option Var → Nat → Bool → Bool → String) : String :=
  match vars with
  | [] => unreachable!
  | x :: _ =>
    dbg_trace s!"THE_Q_SERIALIZE: formatting for var {x}"
    let (rstrPreds, bodyPreds) := extractFromGuard inner 
    dbg_trace s!"THE_Q_SERIALIZE: split into rstr({rstrPreds.length}) and body({bodyPreds.length})"
    
    let baseIndent := makeIndent ind
    let contentIndent := makeIndent (ind + 2)
    
    let rstrStr := match rstrPreds with
    | [] => ""
    | preds => 
      let substitutedPreds := substituteInFormula (Formula.conj preds) x "s"
      let str := formatFn substitutedPreds none (ind + 4) false false
      str.trim
    
    let bodyStr := match bodyPreds with
    | [] => ""
    | _ => formatFn (Formula.conj bodyPreds) none (ind + 4) false false

    s!"{baseIndent}?[S]:(/* the_q */\n" ++
    s!"{contentIndent}S=^[s]:(\n" ++
    s!"{contentIndent}  {rstrStr}) &\n" ++
    s!"{contentIndent}size(S)=1 &\n" ++
    s!"{contentIndent}?[{x}]:(\n" ++
    s!"{contentIndent}  S({x})" ++
    (if bodyStr == "" then 
      " /* the_q NO BODY */\n{contentIndent})" 
    else 
      s!" & /* the_q BODY */\n{bodyStr}\n{contentIndent})") ++
    ")"

end PWL.Transform.Serialize

export PWL.Transform.Serialize (formatTheQ)
