import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformSerializeBase
import Mrs.Hof

namespace PWL.Transform.Serialize

open MRS (EP Var)
open HOF (lastTwoChars)
open PWL.Transform.Serialize (makeIndent normalizePredicate)

def formatConjunction (ep : EP) (indent : Nat) : String :=
  dbg_trace s!"CONJ FORMAT: {ep.predicate} with args {ep.rargs.map (fun (n,v) => s!"{n}={v.sort}{v.id}")}"
  let baseIndent := makeIndent indent
  match ep.predicate with
  | "implicit_conj" | "_implicit_conj" | "and_c" | "_and_c" => 
    dbg_trace "-> matched conjunction"
    let arg0 := ep.rargs.find? (fun p => p.1 == "ARG0")
    let arg1 := ep.rargs.find? (fun p => p.1 == "ARG1")
    let arg2 := ep.rargs.find? (fun p => p.1 == "ARG2")
    match arg0, arg1, arg2 with 
    | some (_, x), some (_, x1), some (_, x2) =>
      dbg_trace s!"-> found args ARG0={x.sort}{x.id} ARG1={x1.sort}{x1.id} ARG2={x2.sort}{x2.id}"
      if x.sort == 'x' && x1.sort == 'x' && x2.sort == 'x' then
        dbg_trace "-> all x-type args confirmed"
        s!"{baseIndent}?[{x}]:(/* {normalizePredicate ep.predicate} */\n{baseIndent}  {x}=^[x]:(\n{baseIndent}    x={x1} | x={x2}))"
      else
        dbg_trace "-> using standard format (not all x-type)"
        s!"{baseIndent}({ep.predicate}({x}) & arg1({x})={x1} & arg2({x})={x2})"
    | _, _, _ => 
      dbg_trace "-> missing required args"
      s!"{baseIndent}{ep.predicate}"
  | _ => s!"{baseIndent}{ep.predicate}"

end PWL.Transform.Serialize

export PWL.Transform.Serialize (formatConjunction)
