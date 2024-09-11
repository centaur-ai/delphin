import Mrs
import Ace

open MRS
open THF


-- set_option pp.oneline true
-- set_option pp.proofs true
-- set_option trace.profiler true in

def solveAndFormat (sentenceNumber : Nat) (mrs : MRS) : IO String := do
  let solveRet <- Utool.solveIt mrs
  match solveRet with
  | Except.ok sols => 
    match sols.get? 0 with
    | some sol => return THF.MRS.format sentenceNumber sol
    | none => unreachable!
  | Except.error e2 => unreachable!

def xform (sentenceNumber : Nat) (str : String) : IO String := do
  let (mrsList : List MRS) <- run_ace str
  let ret <- match mrsList.head? with
      | some firstMrs => solveAndFormat sentenceNumber firstMrs
      | none => unreachable!
  return ret

def mapWithIndexM [Monad m] (xs : List α) (f : Nat → α → m β) : m (List β) := do
  let rec loop : List α → Nat → m (List β)
    | [],    _ => pure []
    | x::xs, i => do
      let y ← f i x
      let ys ← loop xs (i+1)
      pure (y::ys)
  loop xs 0

def main : IO Unit := do
 let sentences := ["Someone who lives in Dreadbury Mansion killed Aunt Agatha.",
                   "Agatha, the butler, and Charles live in Dreadbury Mansion, and are the only people who live therein.",
                   "A killer always hates his victim, and is never richer than his victim.",
                   "Charles hates no one that Aunt Agatha hates.",
                   "Agatha hates everyone except the butler.",
                   "The butler hates everyone not richer than Aunt Agatha.",
                   "The butler hates everyone Aunt Agatha hates.",
                   "No one hates everyone.",
                   "Agatha is not the butler.",
                   "Therefore : Agatha killed herself."]

 let sentences <- mapWithIndexM sentences xform
 let header0 := "thf(x_decl,type,x : $tType)."
 let header1 := "thf(e_decl,type,e : $tType)."
 let header2 := "thf(string_decl,type,string : $i)."
 let header3 := "thf(int_to_e_decl,type,int_to_e: $int > e)."
 let headers := header0 ++ "\n" ++ header1 ++ "\n" ++ header2 ++ "\n" ++ header3 ++ "\n\n" ++ THF.libraryRoutines ++ "\n"
 IO.FS.writeFile "thf-outputs/sentences.p" ((sentences.foldl (fun acc str => acc ++ str ++ "\n") headers))
 return ()
  
-- #eval main
