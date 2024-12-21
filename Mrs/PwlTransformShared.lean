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

structure Stats where
  counts : Lean.HashMap Nat Nat := Lean.HashMap.empty
  deriving Inhabited 

def addStat (stats : Stats) (key : Nat) : Stats :=
  { counts := match stats.counts.find? key with
    | none => stats.counts.insert key 1
    | some n => stats.counts.insert key (n + 1) }

structure CompoundMatch where
  compound : EP
  properQ1 : EP
  properQ2 : EP
  named1   : EP
  named2   : EP
  deriving Repr, Inhabited, BEq

instance : ToString CompoundMatch where
  toString m := s!"CompoundMatch(compound.label: {m.compound.label}, properQ1.label: {m.properQ1.label}, compound: {m.compound})"

instance : ToString (List CompoundMatch) where
  toString xs := String.intercalate ", " (xs.map toString)

def shouldRemove (p : EP) (pat : CompoundMatch) : Bool :=
  p == pat.compound || p == pat.properQ1 || p == pat.properQ2 || 
  p == pat.named1 || p == pat.named2

def getCompoundPattern (preds : List EP) (c : EP) (hm : Multimap Var EP) : Option CompoundMatch :=
  if c.predicate != "compound" && c.predicate != "_compound" then none else
  (match c.rargs with
  | (_, x1) :: (_, x2) :: _ =>
    dbg_trace ("Found compound args: " ++ toString x1 ++ ", " ++ toString x2)
    if x1.sort == 'x' && x2.sort == 'x' then
      let handlePreds := hm.keys.foldl (fun acc k =>
        match hm.find? k with
        | some preds => acc ++ preds
        | none => acc) []

      let preds1 := handlePreds.filter fun p => p.rargs.any fun (_, v2) => v2 == x1
      let preds2 := handlePreds.filter fun p => p.rargs.any fun (_, v2) => v2 == x2

      let properQ1 := preds1.find? fun p => p.predicate.endsWith "_q"
      let properQ2 := preds2.find? fun p => p.predicate.endsWith "_q"
      let named1 := preds1.find? fun p => p.predicate == "named"
      let named2 := preds2.find? fun p => p.predicate == "named"

      match properQ1, properQ2, named1, named2 with
      | some q1, some q2, some n1, some n2 =>
        match n1.carg, n2.carg with
        | some s1, some s2 => some ⟨c, q1, q2, n1, n2⟩
        | _, _ => none
      | _, _, _, _ => none
    else none
  | _ => none)

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

def getOrderedQuantArgs (args : List (String × Var)) : Option (Var × Var × Var) :=
  let arg0 := args.find? (fun p => p.1 == "ARG0")
  let rstr := args.find? (fun p => p.1 == "RSTR")
  let body := args.find? (fun p => p.1 == "BODY") 
  match arg0, rstr, body with 
  | some (_, a), some (_, r), some (_, b) => some (a, r, b)
  | _, _, _ => none

end PWL.Transform

export PWL.Transform (normalizedPredName joinSep joinComma reformQuotedPair getArg orderArgs getOrderedQuantArgs)
