import ErdosProblems.Erdos118.StrictSharedFirstLeaves
import ErdosProblems.Erdos118.StrictOpeningShape
import ErdosProblems.Erdos118.StrictTargetCheckpoint
import ErdosProblems.Erdos118.PendingRootSuccessor

/-! Both paused source right next-body certificates, retaining their
full root tails, and the corresponding target next-root identities. -/

namespace Erdos118.StrictMarkerRequests

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns LastBodyRefinement

structure RightCertificate (H : Set ℕ) (B : SimpleGraph G) (S P : Pending)
    (c : ℕ) (rest : List ℕ) (hR : P.roots = c :: rest) where
  bound : ℕ
  certificate : ∀ Q : Stem, ∀ v : List ℕ,
    Q.root = P.position.stem.root → Q.done.length = c - 1 →
    Q.ordinary = P.position.ordinary ++ v →
    (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, bound < x) →
    ∃ A : StemResponses.Setup P.position (c - 1), A.newWord = v ∧
      A.stem.ordinary = Q.ordinary ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf S, .leaf P) (.leaf S, .body (ofStem P c rest hR A)) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside
        (.leaf S, .body (ofStem P c rest hR A))) true

theorem capture {H : Set ℕ} (B : SimpleGraph G) (S P : Pending)
    (c : ℕ) (rest : List ℕ) (hR : P.roots = c :: rest) (hL : P.leaves = [])
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (.leaf S, .leaf P)) :
    Nonempty (RightCertificate H B S P c rest hR) := by
  obtain ⟨b, hb⟩ := StemReplay.right_body_words_step
    (GraphPayoff.payoff B .inside) (.leaf S) P c rest hR hL hblue
  exact ⟨⟨b, hb⟩⟩

theorem old_next {H : Set ℕ} {B : SimpleGraph G} (O : StrictInitialOpening.Opening H B) :
    ∃ rest : List ℕ, O.opening.checkpoint.right.roots = O.reserve.labels.next :: rest := by
  have hstem : O.opening.checkpoint.right.position.stem = O.prepared.body.stem :=
    O.opening.checkpoint.sameBody.stem.trans O.opening.source.stem_eq
  have hlabel := (congrArg Stem.rootLabel hstem).trans O.reserve.lower
  have hindex := (congrArg (fun S : Stem ↦ S.done.length + 1) hstem).trans
    (O.reserve.index_of_rank O.prepared.body O.prepared.bodyRank)
  apply PendingRootSuccessor.of_gap _ O.opening.checkpoint.rightExact O.reserve.labels.next
  · rw [hlabel]
    exact O.reserve.labels.nextLower
  · rw [hindex]
    exact O.reserve.labels.increasing
  · intro x hx hlt
    rw [hlabel] at hx
    rw [hindex] at hlt
    exact (O.reserve.labels.lowerGap x hx).resolve_left (not_le_of_gt hlt)

theorem inserted_next {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    (W : StrictSecondOpening.Opening J) :
    ∃ rest : List ℕ, W.opening.checkpoint.right.roots = W.reserve.labels.next :: rest := by
  have hstem : W.opening.checkpoint.right.position.stem = W.prepared.body.stem :=
    W.opening.checkpoint.sameBody.stem.trans W.opening.source.stem_eq
  have hlabel := (congrArg Stem.rootLabel hstem).trans W.reserve.lower
  have hindex := (congrArg (fun S : Stem ↦ S.done.length + 1) hstem).trans
    (W.reserve.index_of_rank W.prepared.body W.prepared.bodyRank)
  apply PendingRootSuccessor.of_gap _ W.opening.checkpoint.rightExact W.reserve.labels.next
  · rw [hlabel]
    exact W.reserve.labels.nextLower
  · rw [hindex]
    exact W.reserve.labels.increasing
  · intro x hx hlt
    rw [hlabel] at hx
    rw [hindex] at hlt
    exact (W.reserve.labels.lowerGap x hx).resolve_left (not_le_of_gt hlt)

structure Requests {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {J : StrictTwoRootRequests.Requests O true} {W : StrictSecondOpening.Opening J}
    {Q : StrictSharedBodyRequests.Requests W} (F : StrictSharedFirstLeaves.Pair Q) where
  oldRest : List ℕ
  oldRoots : O.opening.checkpoint.right.roots = O.reserve.labels.next :: oldRest
  oldNonempty : oldRest ≠ []
  oldLeaves : O.opening.checkpoint.right.leaves = []
  old : RightCertificate O.prepared.alphabet O.prepared.graph F.oldLeft
    O.opening.checkpoint.right O.reserve.labels.next oldRest oldRoots
  insertedRest : List ℕ
  insertedRoots : W.opening.checkpoint.right.roots = W.reserve.labels.next :: insertedRest
  insertedNonempty : insertedRest ≠ []
  insertedLeaves : W.opening.checkpoint.right.leaves = []
  inserted : RightCertificate W.prepared.alphabet W.prepared.graph F.insertedLeft
    W.opening.checkpoint.right W.reserve.labels.next insertedRest insertedRoots

theorem exists_requests {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {J : StrictTwoRootRequests.Requests O true} {W : StrictSecondOpening.Opening J}
    {Q : StrictSharedBodyRequests.Requests W} (F : StrictSharedFirstLeaves.Pair Q)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = true) : Nonempty (Requests F) := by
  obtain ⟨r, hr⟩ := old_next O
  obtain ⟨s, hs⟩ := inserted_next W
  have hL := (StrictOpeningShape.old_test O true hall).mpr rfl
  have hL' := (StrictOpeningShape.inserted_test W hall).mpr rfl
  obtain ⟨R⟩ := capture O.prepared.graph F.oldLeft O.opening.checkpoint.right
    O.reserve.labels.next r hr hL F.oldHandoff
  obtain ⟨S⟩ := capture W.prepared.graph F.insertedLeft W.opening.checkpoint.right
    W.reserve.labels.next s hs hL' F.insertedHandoff
  obtain ⟨hrold, hrnew⟩ := StrictOpeningShape.last_future_roots W hall
  have hrne : r ≠ [] := by intro he; simp [hr, he] at hrold
  have hsne : s ≠ [] := by intro he; simp [hs, he] at hrnew
  exact ⟨{
    oldRest := r, oldRoots := hr, oldNonempty := hrne, oldLeaves := hL, old := R
    insertedRest := s, insertedRoots := hs, insertedNonempty := hsne
    insertedLeaves := hL', inserted := S }⟩

theorem target_left_next {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value} {W : StrictSecondOpening.Opening J}
    {d : ℕ} (C : StrictTargetCheckpoint.Checkpoint W d) :
    C.left.roots = [O.reserve.labels.next] ∧ C.left.leaves = [] := by
  obtain ⟨c, hR, hL⟩ := C.critical
  have hc := ExactSlots.pending_next_last_root C.left C.leftExact hR
  rw [C.leftRoot, O.reserve.labels.last] at hc
  rw [← hc] at hR
  exact ⟨hR, hL⟩

theorem target_right_next {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {J : StrictTwoRootRequests.Requests O true} {W : StrictSecondOpening.Opening J}
    {d : ℕ} (C : StrictTargetCheckpoint.Checkpoint W d) (hanchor : W.anchorRank = J.rank + 1) :
    (∃ rest : List ℕ, C.right.roots = W.reserve.labels.next :: rest) ∧ C.right.leaves = [] := by
  refine ⟨?_, C.last.mpr rfl⟩
  apply PendingRootSuccessor.of_rank C.right C.rightExact W.reserve.labels.next
  · rw [C.rightRoot]
    exact W.reserve.labels.nextUpper
  · rw [C.rank, C.rightRoot, W.reserve.labels.upperRank, hanchor]

end Erdos118.StrictMarkerRequests
