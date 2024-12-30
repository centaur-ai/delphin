import Mrs.Basic
import Mrs.PwlTypes
import Mrs.PwlTransformShared
import Mrs.PwlTransformMinScoping_Core
import Util.InsertionSort

namespace PWL.Transform.MinScoping

open MRS (EP Var)
open InsertionSort
open PWL.Transform
open Lean (HashMap)

partial def findConnectedWithFilter (filter : List EP) (pred : EP) (seen : List EP) : List EP :=
  let myEvents := getEventVars pred
  dbg_trace s!"MINSCOPE:  Finding connected for {pred.predicate} with events {myEvents}"

  let directlyConnected := filter.filter fun p => 
    if seen.contains p then 
      dbg_trace s!"MINSCOPE:    Skipping {p.predicate} - already seen"
      false 
    else
      let theirEvents := getEventVars p
      let eventMatches := myEvents.map fun myE => 
        theirEvents.any fun theirE => 
          let isMatch := myE == theirE
          dbg_trace s!"MINSCOPE:      Comparing events {myE} == {theirE}: {isMatch}"
          isMatch
      let isConnected := eventMatches.any id
      dbg_trace s!"MINSCOPE:    Checking {p.predicate} with events {theirEvents}, connected? {isConnected}"
      isConnected

  let seenWithMe := pred :: seen
  dbg_trace s!"MINSCOPE:    Directly connected: {directlyConnected.map (·.predicate)}"
  dbg_trace s!"MINSCOPE:    Already seen: {seenWithMe.map (·.predicate)}"
  
  let nextGroups := directlyConnected.foldl (fun acc p =>
    if acc.contains p then acc
    else findConnectedWithFilter filter p acc
  ) seenWithMe

  dbg_trace s!"MINSCOPE:    Returning group: {nextGroups.map (·.predicate)}"
  nextGroups

partial def findAllGroupsWithFilter (filter : List EP) (remaining : List EP) (processedGroups : List (List EP)) : List (List EP) :=
  match remaining with
  | [] => 
    dbg_trace s!"MINSCOPE:  Found all groups: {processedGroups.map (fun g => g.map (·.predicate))}"
    processedGroups
  | p :: ps =>
    dbg_trace s!"MINSCOPE:  Processing {p.predicate}"
    if processedGroups.any (·.contains p) then
      dbg_trace s!"MINSCOPE:    Already in a group, skipping"
      findAllGroupsWithFilter filter ps processedGroups
    else
      let pEvents := getEventVars p
      if pEvents.isEmpty then
        dbg_trace s!"MINSCOPE:    No events, creating singleton group"
        findAllGroupsWithFilter filter ps ([p] :: processedGroups)
      else
        dbg_trace s!"MINSCOPE:    Finding connected group starting with {p.predicate}"
        let connected := findConnectedWithFilter filter p []
        dbg_trace s!"MINSCOPE:    Found group: {connected.map (·.predicate)}"
        findAllGroupsWithFilter filter 
          (ps.filter (fun r => !connected.contains r))
          (connected :: processedGroups)

def findEventGroups (preds : List EP) : List (List EP) :=
  dbg_trace s!"MINSCOPE:findEventGroups starting with {preds.length} predicates"
  
  let allEventPreds := preds.filter (fun p => 
    let evs := getEventVars p
    dbg_trace s!"MINSCOPE:  Checking events for {p.predicate}: {evs}"
    !evs.isEmpty)
  dbg_trace s!"MINSCOPE:  All event-containing predicates: {allEventPreds.map (·.predicate)}"

  findAllGroupsWithFilter allEventPreds preds []

end PWL.Transform.MinScoping

export PWL.Transform.MinScoping (findEventGroups)
