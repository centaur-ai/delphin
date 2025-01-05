import Mrs
import Ace
import Util.InsertionSort
import Mrs.Pwl

open MRS
open PWL 
open InsertionSort

def solveAndFormat (sentenceNumber : Nat) (mrs : MRS) : IO (String × List String × List Var) := do
  let solveRet <- Utool.solveIt mrs
  match solveRet with
  | Except.ok sols => 
    match sols.get? 0 with
    | some sol => 
      let (formatted, strings, vars) := PWL.MRS.format sentenceNumber sol
      return (formatted, strings, vars)
    | none => unreachable!
  | Except.error _ => unreachable!

def xform (sentenceNumber : Nat) (parseNumber : Nat) (str : String) : IO (Nat × (String × List String × List Var)) := do
  let (mrsList : List MRS) <- run_ace str
  match mrsList.get? parseNumber with
    | some selectedMrs => do
      let ret <- solveAndFormat sentenceNumber selectedMrs
      return (sentenceNumber, ret)
    | none => unreachable!

def mapWithIndexM [Monad m] (xs : List α) (f : Nat → α → m β) : m (List β) := do
  let rec loop : List α → Nat → m (List β)
    | [],    _ => pure []
    | x::xs, i => do
      let y ← f i x
      let ys ← loop xs (i+1)
      pure (y::ys)
  loop xs 0

instance : Ord (Nat × Var) where
  compare := fun a b =>
    match compare a.1 b.1 with
    | .eq => compare a.2 b.2
    | ord => ord

def addSentenceNumber (sentenceNumber : Nat) (l : List Var) : List (Nat × Var) :=
  l.map (fun var => (sentenceNumber,var))

def main : IO Unit := do
 let sentencesText := [
                      "Someone who lives in Dreadbury Mansion killed Aunt Agatha.", -- 0
                      "Agatha, the butler, and Charles live in Dreadbury Mansion, and are the only people who live therein.", -- 1
                      "A killer always hates his victim, and is never richer than his victim.", -- 2
                      "Charles hates nobody that Aunt Agatha hates.", -- 3
                      "Agatha hates everyone except the butler.", -- 4
                      "The butler hates everyone not richer than Aunt Agatha.", -- 5
                      "The butler hates everyone Aunt Agatha hates.", -- 6
                      "No one hates everyone.", -- 7
                      "Agatha is not the butler.", -- 8
                      -- "Therefore : Agatha killed herself." -- 9
                      "Who killed Agatha?" -- 9
                   ] 

 let parseNumbers : List Nat := [1, 0, 0, 0, 0,  1, 0, 0, 0, 0]

 -- let (sentences : List (Nat × (String × (List String) × (List Var)))) <- mapWithIndexM sentencesText xform

 let (sentences : List (Nat × (String × (List String) × (List Var)))) <- 
   mapWithIndexM sentencesText (fun idx str => 
     let parseNumber := parseNumbers.get? idx |>.getD 0
     xform idx parseNumber str)
 
 -- Collect event variables
 let (eSet : List (Nat × Var)) := sentences.foldl (fun acc tup => 
                                                    let (trip : (String × (List String) × (List Var))) := tup.snd
                                                    acc ++ (addSentenceNumber tup.fst trip.snd.snd)) []
 -- Collect string constants
 let (iSet : List String) := sentences.foldl (fun acc tup => 
                                               let (trip : (String × (List String) × (List Var))) := tup.snd
                                               let (strList : (List String)) := trip.snd.fst
                                               acc ++ strList) []

 -- Just combine all the sentence content
 let sentenceContent := sentences.foldl (fun acc pair => acc ++ pair.snd.fst ++ "\n;\n") ""
 let finalContent := sentenceContent
 
 IO.FS.writeFile "pwl-outputs/sentences.pwl" finalContent
 return ()
