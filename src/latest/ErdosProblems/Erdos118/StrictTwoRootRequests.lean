import ErdosProblems.Erdos118.StrictUpperRoot
import ErdosProblems.Erdos118.StrictInsertedRoot
import ErdosProblems.Erdos118.InsertedAlignment
import ErdosProblems.Erdos118.AlignedRightPreparation

/-! Save the old source next-body certificate and both localized right
root requests before either actual right-root label is submitted. -/

namespace Erdos118.StrictTwoRootRequests

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns InsideCounts LastBodyRefinement CriticalPair
open AlignedRightPreparation (RootCertificate)

def target {H : Set ℕ} {B : SimpleGraph G} (O : StrictInitialOpening.Opening H B) : Pending :=
  applyBody (ofRoot O.target.rootSetup) O.opening.target

structure Requests {H : Set ℕ} {B : SimpleGraph G} (O : StrictInitialOpening.Opening H B)
    (value : Bool) where
  oldRoot : ℕ
  oldRootEq : O.opening.checkpoint.left.roots = [oldRoot]
  oldBound : ℕ
  oldCertificate : InsertedAlignment.NextCertificate O.prepared.alphabet O.prepared.graph
    O.opening.checkpoint.left O.opening.checkpoint.right oldRoot oldRootEq oldBound
  alphabet : Set ℕ
  subset : alphabet ⊆ O.prepared.alphabet
  infinite : alphabet.Infinite
  above : ∀ x ∈ alphabet, oldBound < x
  graph : SimpleGraph G
  subgraph : graph ≤ B
  triangleFree : graph.CliqueFree 3
  upper : RootCertificate alphabet graph (target O)
  rank : ℕ
  positive : 0 < rank
  bounded : rank < upper.size + 1
  lastBound : value = true → rank + 1 < upper.size + 1
  exactRank : ∀ S T : Completed, GraphPayoff.payoff graph .inside S T = true →
    1 < S.stem.rootLabel.length → T.stem.rootLabel.length = upper.size + 1 →
    bodyRank T.stem (lastLabel S).length = rank ∧
      (last T.stem (lastLabel S).length = true → rank + 1 < upper.size + 1)
  inserted : StrictInsertedRoot.Opening H alphabet B O.initial
    O.opening.checkpoint.left O.buffer oldBound

theorem exists_requests {H : Set ℕ} {B : SimpleGraph G} (O : StrictInitialOpening.Opening H B)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hstrict : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (value : Bool) (hcolor : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      last T.stem (lastLabel S).length = value) : Nonempty (Requests O value) := by
  obtain ⟨c, hR, hL⟩ := O.opening.checkpoint.criticalLeft
  obtain ⟨b, hb⟩ := InsertedAlignment.certificate O.prepared.graph
    O.opening.checkpoint.left O.opening.checkpoint.right c hR hL O.opening.checkpoint.command
  obtain ⟨l, K, hKP, hK, hKb, C, hCB, hC, _, v, hv, hvl, hlast, d, hcert, hexact⟩ :=
    StrictUpperRoot.localize O hB hinit hstrict value hcolor b
  let I : RootCertificate K C (target O) := ⟨l, d, hcert⟩
  have hKH : K ⊆ H := hKP.trans (O.prepared.subset.trans O.subset)
  obtain ⟨J⟩ := StrictInsertedRoot.exists_opening hK hKH B hB hinit hstrict O.initial O.positive
    O.opening.checkpoint.left c hR O.opening.checkpoint.leftExact O.buffer O.freshLeft b
  exact ⟨{
    oldRoot := c, oldRootEq := hR, oldBound := b, oldCertificate := hb
    alphabet := K, subset := hKP, infinite := hK, above := hKb
    graph := C, subgraph := hCB, triangleFree := hC, upper := I, rank := v
    positive := hv, bounded := hvl, lastBound := hlast, exactRank := hexact, inserted := J }⟩

end Erdos118.StrictTwoRootRequests
