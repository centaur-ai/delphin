import Mrs.Basic
import Mrs.PwlTypes
import Mrs.Hof
import Util.InsertionSort

namespace PWL.Transform

open MRS (Var EP Constraint MRS)
open MM (Multimap)
open Lean (Format HashMap)
open InsertionSort
open HOF (lastTwoChars)

instance : Hashable EP where
  hash e := mixHash 
    (hash e.predicate) 
    (mixHash (hash e.label)
     (mixHash (hash e.rargs)
      (mixHash (hash e.link) (hash e.carg))))

structure Stats where
  counts : Lean.HashMap Nat Nat := Lean.HashMap.empty
  deriving Inhabited 

def addStat (stats : Stats) (key : Nat) : Stats :=
  { counts := match stats.counts.find? key with
    | none => stats.counts.insert key 1
    | some n => stats.counts.insert key (n + 1) }

structure CompoundHandleInfo where
  predicate : EP 
  handle : Var
  deriving Repr, Inhabited, BEq

structure CompoundMatch where
  compound : EP
  properQ1 : CompoundHandleInfo
  properQ2 : CompoundHandleInfo
  named1   : CompoundHandleInfo
  named2   : CompoundHandleInfo
  deriving Repr, Inhabited, BEq

def MAX_DEPTH : Nat := 999999

structure DepthMap where 
  depths : HashMap Var Nat

instance : ToString (HashMap Var Nat) where
  toString m := toString (m.toList)

instance : ToString CompoundMatch where
  toString m := s!"CompoundMatch(compound.label: {m.compound.label}, properQ1.label: {m.properQ1.predicate.label}, compound: {m.compound})"

instance : ToString (List CompoundMatch) where
  toString xs := String.intercalate ", " (xs.map toString)

def shouldRemove (p : EP) (pat : CompoundMatch) : Bool :=
  p == pat.compound || p == pat.properQ1.predicate || p == pat.properQ2.predicate || 
  p == pat.named1.predicate || p == pat.named2.predicate

def predHandles (handles : List Var) (hm : Multimap Var EP) : HashMap EP Var :=
  handles.foldl (fun acc h =>
    match hm.find? h with
    | some preds => preds.foldl (fun acc2 p => acc2.insert p h) acc
    | none => acc) HashMap.empty

partial def findHandleDepth (pred : EP) (hm : Multimap Var EP) (rootHandle : Var) : Nat :=
  let rec findDepth (handle : Var) (seen : List Var) : Nat :=
    if handle == rootHandle then 0
    else if seen.contains handle then 999999
    else
      -- Find all predicates at this handle
      match hm.find? handle with
      | none => 999999
      | some preds =>
        -- Find predicates that reference other handles and get min depth
        let minChildDepth := preds.foldl (fun minD curP =>
          let childHandles := curP.rargs.filter (fun (n, v) => v.sort == 'h') |>.map (·.2)
          let childDepths := childHandles.map (fun h => findDepth h (handle :: seen))
          let childMin := childDepths.foldl min 999999
          min minD childMin
        ) 999999
        minChildDepth + 1
  findDepth pred.label []

def getOrderedQuantArgs (args : List (String × Var)) : Option (Var × Var × Var) :=
  let arg0 := args.find? (fun p => p.1 == "ARG0")
  let rstr := args.find? (fun p => p.1 == "RSTR")
  let body := args.find? (fun p => p.1 == "BODY") 
  match arg0, rstr, body with 
  | some (_, a), some (_, r), some (_, b) => some (a, r, b)
  | _, _, _ => none

partial def computeDepthMap (rootHandle : Var) (hm : Multimap Var EP) : DepthMap := 
  let rec computeDepth (handle : Var) (parentHandle : Option Var) (seen : List Var) (acc : HashMap Var Nat) : HashMap Var Nat :=
    dbg_trace s!"Computing depth for {handle} from {parentHandle} (root={rootHandle})"
    if handle == rootHandle then acc
    else if seen.contains handle then acc
    else 
      match hm.find? handle with 
      | none => acc
      | some preds =>
        let depth := match parentHandle with 
        | none => 1  -- Direct from root
        | some p => match acc.find? p with
          | some d => d + 1
          | none => 1
        let newAcc := acc.insert handle depth

        -- Process predicates and update depths map
        preds.foldl (fun innerAcc pred =>
          dbg_trace s!"  Processing {pred.predicate} at {handle} with {pred.rargs}"
          if lastTwoChars pred.predicate == "_q" then
            let rstrArg := pred.rargs.find? (fun p => p.1 == "RSTR")
            let bodyArg := pred.rargs.find? (fun p => p.1 == "BODY")
            match rstrArg, bodyArg with
            | some (_, rstr), some (_, body) =>
              dbg_trace s!"  Found quantifier path: RSTR={rstr}, BODY={body}"
              let acc1 := computeDepth rstr (some handle) (handle :: seen) innerAcc
              computeDepth body (some handle) (handle :: seen) acc1
            | _, _ => innerAcc
          else innerAcc
        ) newAcc

  let rootDepths := HashMap.empty.insert rootHandle 0
  let finalDepths := match hm.find? rootHandle with
  | none => rootDepths
  | some rootPreds =>
    rootPreds.foldl (fun acc pred =>
      pred.rargs.foldl (fun inner arg =>
        if arg.2.sort == 'h' then
          computeDepth arg.2 none [] inner
        else inner
      ) acc
    ) rootDepths

  dbg_trace s!"Final depths: {finalDepths}"
  DepthMap.mk finalDepths

def getCompoundPattern (preds : List EP) (c : EP) (hm : Multimap Var EP) (dm : DepthMap) : Option CompoundMatch := 
  dbg_trace s!"GET_PATTERN start: compound={c.predicate}({c.label})"
  if c.predicate != "compound" && c.predicate != "_compound" then 
    dbg_trace "GET_PATTERN rejected: not a compound predicate"
    none
  else match c.rargs with
  | (_, x1) :: (_, x2) :: _ => 
    dbg_trace s!"GET_PATTERN compound args: x1={x1}, x2={x2}"
    if x1.sort == 'x' && x2.sort == 'x' then
      -- Find all predicates that involve these variables
      let preds1 := preds.filter (fun p => p.rargs.any (fun arg => arg.2 == x1))
      let preds2 := preds.filter (fun p => p.rargs.any (fun arg => arg.2 == x2))
      
      -- Find proper_q and named predicates for each variable based on dependencies
      let named1 := preds1.find? (fun p => p.predicate == "named" || p.predicate == "_named")
      let named2 := preds2.find? (fun p => p.predicate == "named" || p.predicate == "_named")

      let properQ1 := preds1.find? (fun p => 
        p.predicate.endsWith "_q" && p.rargs.any (fun arg => arg.1 == "ARG0" && arg.2 == x1))
      let properQ2 := preds2.find? (fun p => 
        p.predicate.endsWith "_q" && p.rargs.any (fun arg => arg.1 == "ARG0" && arg.2 == x2))

      dbg_trace s!"GET_PATTERN found components:"
      dbg_trace s!"  named1: {named1.map (fun p => (p.label, p.carg))}"
      dbg_trace s!"  named2: {named2.map (fun p => (p.label, p.carg))}"
      dbg_trace s!"  properQ1: {properQ1.map (fun p => p.label)}"
      dbg_trace s!"  properQ2: {properQ2.map (fun p => p.label)}"

      match properQ1, properQ2, named1, named2 with
      | some q1, some q2, some n1, some n2 =>
        -- Get depths
        let d1 := match dm.depths.find? q1.label with | some d => d | none => MAX_DEPTH
        let d2 := match dm.depths.find? q2.label with | some d => d | none => MAX_DEPTH
        
        dbg_trace s!"GET_PATTERN checking depths: Q1={d1}({q1.label}) Q2={d2}({q2.label})"

        -- Create handle infos and return pattern
        let h1 := CompoundHandleInfo.mk q1 q1.label 
        let h2 := CompoundHandleInfo.mk q2 q2.label
        let h3 := CompoundHandleInfo.mk n1 n1.label
        let h4 := CompoundHandleInfo.mk n2 n2.label
        
        if d1 ≤ d2 then 
          some ⟨c, h1, h2, h3, h4⟩
        else 
          some ⟨c, h2, h1, h4, h3⟩
        
      | _, _, _, _ =>
        dbg_trace s!"GET_PATTERN pattern match failed - missing components"
        none
    else none
  | _ => none

inductive Formula where
  | atom : EP → Formula
  | conj : List Formula → Formula 
  | scope : List Var → Option String → Formula → Formula
  deriving Inhabited

mutual
  partial def beqFormula : Formula → Formula → Bool
    | Formula.atom ep1, Formula.atom ep2 => ep1 == ep2
    | Formula.conj fs1, Formula.conj fs2 => beqFormulaList fs1 fs2
    | Formula.scope vs1 q1 f1, Formula.scope vs2 q2 f2 =>
        vs1 == vs2 && q1 == q2 && beqFormula f1 f2
    | _, _ => false

  partial def beqFormulaList : List Formula → List Formula → Bool
    | [], [] => true
    | f1::fs1, f2::fs2 => beqFormula f1 f2 && beqFormulaList fs1 fs2
    | _, _ => false
end

instance : BEq Formula where
  beq := beqFormula

instance : BEq (List Formula) where
  beq := beqFormulaList

mutual
  partial def formulaToString : Formula → String
    | Formula.atom ep => toString ep
    | Formula.conj fs => "(" ++ listFormulaToString fs ++ ")"
    | Formula.scope vars none inner => s!"?[{vars}]: {formulaToString inner}"
    | Formula.scope vars (some q) inner => s!"?[{vars}]: /* {q} */ {formulaToString inner}"

  partial def listFormulaToString : List Formula → String
    | [] => ""
    | [f] => formulaToString f 
    | f :: fs => formulaToString f ++ " & " ++ listFormulaToString fs
end

instance : ToString Formula where
  toString := formulaToString

instance : ToString (List Formula) where
  toString fs := "[" ++ String.intercalate ", " (fs.map formulaToString) ++ "]"

def Formula.isAtom : Formula → Bool
  | atom _ => true 
  | _ => false

def Formula.isConj : Formula → Bool 
  | conj _ => true
  | _ => false

def Formula.hasScope : Formula → Bool
  | scope _ _ _ => true
  | _ => false

def Formula.getScopedFormula : Formula → Option Formula
  | scope _ _ f => some f
  | _ => none

def Formula.getScopeVars : Formula → Option (List Var)
  | scope vs _ _ => some vs
  | _ => none

def Formula.isEmptyConj : Formula → Bool
  | conj [] => true
  | conj [f] => f.isEmptyConj
  | _ => false

partial def Formula.removeEmptyConj : Formula → Formula 
  | atom ep => atom ep
  | conj [] => conj []  
  | conj [f] => f.removeEmptyConj
  | conj fs =>
    let nonEmpty := fs.filter (fun f => !f.isEmptyConj)
    match nonEmpty with
    | [] => conj []
    | [f] => f.removeEmptyConj
    | fs => conj (fs.map Formula.removeEmptyConj)
  | scope vars quant inner => 
    scope vars quant (inner.removeEmptyConj)

private def substituteVar (old new : Var) (args : List (String × Var)) : List (String × Var) :=
  dbg_trace s!"substituteVar old:{old} new:{new} args:{args}"
  args.map fun (name, var) => 
    let res := if var == old then (name, new) else (name, var)
    dbg_trace s!"  {name}: {var} => {res.2}"
    res

partial def Formula.substitute (old new : Var) : Formula → Formula
  | atom ep => 
    dbg_trace s!"substitute in atom EP {ep.predicate}, args: {ep.rargs}"
    let newArgs := substituteVar old new ep.rargs
    dbg_trace s!"  after substitution: {newArgs}"
    atom { ep with rargs := newArgs }
  | conj fs => 
    dbg_trace "substitute in conj"
    conj (fs.map (Formula.substitute old new))
  | scope vars quant inner => 
    dbg_trace s!"substitute in scope: vars {vars}"
    let newVars := vars.map fun v => if v == old then new else v
    dbg_trace s!"  after var substitution: {newVars}"
    scope newVars quant (inner.substitute old new)

def removeExtraQuotes (s : String) : String :=
  if s.startsWith "\"" && s.endsWith "\"" then s.extract ⟨1⟩ ⟨s.length - 1⟩ else s

def normalizedPredName (predicate : String) : String :=
  if predicate.startsWith "_" then predicate.drop 1 else predicate

def joinSep (l : List String) (sep : String) : String := 
  l.foldr (fun s r => (if r == "" then s else r ++ sep ++ s)) ""

def joinComma (l : List String) : String := 
  joinSep l ","

def reformQuotedPair (s : String) : String :=
  let parts := String.split s (· == ' ')
  let unquoted := parts.map removeExtraQuotes
  "\"" ++ " ".intercalate unquoted ++ "\""

def getArg (ep : EP) (name : String) : Option Var :=
  ep.rargs.find? (fun r => r.1 == name)
  |>.map (fun r => r.2)

def orderArgs (args : List (String × Var)) : List (String × Var) :=
  args.filter (fun a => a.1.startsWith "ARG") |> insertionSort

def getVarDeps (ep : EP) : List Var :=
  ep.rargs.filter (fun arg => arg.2.sort == 'x' || arg.2.sort == 'e' || arg.2.sort == 'i')
    |>.map (·.2)

def getScopableArgs (ep : EP) : List (String × Var) :=
  ep.rargs.filter (fun arg => arg.2.sort == 'x' || arg.2.sort == 'e' || arg.2.sort == 'i')

end PWL.Transform
