import ErdosProblems.Erdos118.Reused591.ReservedInsidePreparation
import ErdosProblems.Erdos118.Reused591.ReservedLateCheckpoint

namespace Erdos118.Reused591

/-!
# The complete reserved insertion through its nonlast opposite critical leaf

The retained virtual prefix is extended by the actual tail-pool path.
Every new coordinate remains above the older pending-response bound.
The resulting critical history and its managed upper origin are both
available for deferred firing and the shared last-marker replay.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem reserved_late_insertion {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a c : ℕ} (L : LastLastLabels H B a)
    (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hopening : origin.position.pending = some ⟨false, .advance a⟩)
    (hboardOrigin : origin.position.board = Board.initial)
    (hmodeOrigin : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lateFirstMarkerColor z = true)
    (hlarge : ∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q →
      q.position.pending = some ⟨false, .advance d⟩ → q.position.board.left.markerEvent = true →
      (∀ k ∈ q.position.board.left.rootLabel,
        k ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    (hfirst : ∀ q v d, (exactGame N blue).FollowStep σ H b origin q →
      (exactGame N blue).FollowStep σ H b q v →
      v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d)
    (hOldBody : old.position.board.left.bodyLabels.length = L.penultimate)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance c⟩) (hc : 0 < c)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hUpperMode : upperOrigin.position.mode = some true)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor L.lower L.marker).runAtoms as = some old.position.board.left)
    (hinc : (L.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) :
    ∃ J, J ⊆ H ∧ J.Infinite ∧ (∀ x ∈ J, max old.position.bound (b old) < x) ∧
      ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q ∧
        (exactGame N blue).ArchitectWins J b σ q ∧ q.position.mode = some true ∧
        q.position.pending = some ⟨false, .advance 0⟩ ∧
        q.position.board.left.rootLabel = L.upper ∧
        q.position.board.left.bodyLabels.length = L.upperPenultimate ∧
        q.position.board.left.relaxed = true ∧ q.position.board.left.NoLeafPending ∧
        q.position.board.right.relaxed = true ∧
        q.position.board.right.lastSelectedBody = q.position.board.right.bodyLabels.length ∧
        (∃ j ∈ q.position.board.right.currentLabel, q.position.board.right.leafIndex < j) ∧
        2 ≤ q.position.board.right.currentLabel.card ∧
        ∃ frontAtoms, LabeledWord.LegalRun
          (LabeledWord.rootRelabel L.upper old.position.board.left) frontAtoms q.position.board.left ∧
          (∀ atom ∈ frontAtoms, atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2) ∧
          ∃ M : Managed N J blue b σ true true upperOrigin.position.board.left q.position.board.right,
            Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin M.target := by
  obtain ⟨J, hJH, hJ, hJfresh, fine, hfromFine, hwinFine, hnFine, hrFine,
      hFineRoot, hFineBody, hFineStrict, frontAtoms, hfrontRun, hfrontPool, M, hMfrom⟩ :=
    reserved_inside_preparation hHN hH blue htri hroot origin old upperOrigin L hwinOrigin
      hopening hboardOrigin hB hfromUpper hOldBody hpUpper hc hUpperInit hUpperMode hraw hinc hpool
  obtain ⟨q, hfq, hp, hqroot, hqbody, hqr, hqno, hqright, hqLastBody, hqLater, hqCard,
      Mq, hMq⟩ := reserved_late_checkpoint hHN hH hJH hJ blue origin fine upperOrigin L
        hwinOrigin hwinFine hfromFine hall hlarge hnFine hrFine hFineRoot hFineBody
        (hFineStrict hfirst) ⟨M, hMfrom⟩
  have hfqH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hfq
  have hfromQ := hfromFine.trans hfqH
  obtain ⟨newAtoms, hnewRun, hnewPool⟩ := follow_word_inputs hfq 0 (fun _ => Nat.zero_le _) false
  have hfullPool : ∀ atom ∈ frontAtoms ++ newAtoms,
      atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2 := by
    intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfrontPool atom ha
    · exact ⟨hJH (hnewPool atom ha).1, hJfresh atom.2 (hnewPool atom ha).1⟩
  exact ⟨J, hJH, hJ, hJfresh, q, hfromQ, hwinFine.of_reachable (exactGame N blue) hfq,
    follow_mode_some hfromQ hmodeOrigin, hp, hqroot, hqbody, hqr, hqno, hqright,
    hqLastBody, hqLater, hqCard, frontAtoms ++ newAtoms, hfrontRun.append hnewRun,
    hfullPool, Mq, hMq⟩

#print axioms reserved_late_insertion

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
