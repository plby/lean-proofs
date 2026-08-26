import ErdosProblems.Erdos591.PreparedLeaf

/-!
# A prepared upper body reply retained while the lower play advances

The upper body request and its overlap label are fixed before the common
marker. The lower play stores a legal execution from that marker to its
current leaf, with all inputs above the old upper bound. This record can
be transported through individual same-body responses and fired at the
last lower selected leaf. No lower continuation is chosen by the record.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

structure PreparedBody (N H : Set ℕ) (blue : SimpleGraph G)
    (b : Concrete.Hist N → ℕ) (σ : (exactGame N blue).ArchitectStrategy) (w : LabeledWord)
    extends PreparedLeaf N H blue b σ w where
  rootLast : ∀ i ∈ w.rootLabel, i ≤ w.bodyLabels.length

namespace PreparedBody

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy} {w v : LabeledWord}

theorem first_eq (P : PreparedBody N H blue b σ w) :
    P.first = P.stem.record P.labels.lower P.labels.marker
      (Parser.normalize P.remainingBodies P.labels.marker) := by
  exact Option.some.inj (P.firstRead.symm.trans (by
    simp [LabeledWord.read, P.stemParser, Parser.step]))

theorem first_leaf (P : PreparedBody N H blue b σ w) : P.first.leafIndex = 0 := by
  simp [P.first_eq, LabeledWord.record, P.stemParser]

theorem currentLabel (P : PreparedBody N H blue b σ w) : w.currentLabel = P.labels.lower := by
  simp [LabeledWord.currentLabel, P.bodyLabels_eq, P.first_eq, LabeledWord.record, P.stemParser]

theorem not_pending (P : PreparedBody N H blue b σ w) (h : w.leafIndex = P.labels.pivot) :
    ¬ Macro.Pending w :=
  last_selected_leaf_not_pending P.labels P.rootLast P.currentLabel h

theorem last_of_not_pending (P : PreparedBody N H blue b σ w) (h : ¬ Macro.Pending w) :
    w.leafIndex = P.labels.pivot := by
  apply le_antisymm P.upto.before
  by_contra hn
  have hlt : w.leafIndex < P.labels.pivot := by omega
  exact h (Or.inr ⟨P.upto.selected, P.labels.pivot, P.upto.mem, hlt⟩)

def move (P : PreparedBody N H blue b σ w) {ys : List (Finset ℕ × ℕ)}
    (h : LabeledWord.LegalRun w ys v) (hbody : v.bodyLabels = w.bodyLabels)
    (hpool : ∀ a ∈ ys, a.2 ∈ H ∧ P.budget < a.2)
    (hup : LabeledWord.UpToLeaf P.labels.pivot v) : PreparedBody N H blue b σ v where
  target := P.target
  side := P.side
  stem := P.stem
  remainingBodies := P.remainingBodies
  budget := P.budget
  lowerSize := P.lowerSize
  upperSize := P.upperSize
  labels := P.labels
  targetPending := P.targetPending
  targetMarker := P.targetMarker
  targetBound := P.targetBound
  targetWinning := P.targetWinning
  stemSame := P.stemSame
  stemParser := P.stemParser
  first := P.first
  firstRead := P.firstRead
  atoms := P.atoms ++ ys
  run := P.run.append h
  bodyLabels_eq := hbody.trans P.bodyLabels_eq
  pool := by
    intro a ha
    exact (List.mem_append.mp ha).elim (P.pool a) (hpool a)
  rootLast := by
    intro i hi
    have hstart := P.run.parser_ne_start (LabeledWord.read_parser_ne_start P.firstRead)
    have hroot := h.rootLabel_eq hstart
    rw [hbody]
    exact P.rootLast i (hroot ▸ hi)
  upto := hup

theorem fire (P : PreparedBody N H blue b σ w) (hHN : H ⊆ N)
    (hinc : w.coordinates.Pairwise (· < ·)) (hlast : w.leafIndex = P.labels.pivot) :
    ∃ q, (exactGame N blue).FollowStep σ H b P.target q ∧ q.position.pending = none ∧
      (q.position.board.get P.side).coordinates = w.coordinates ∧
      (q.position.board.get P.side).relaxed = true ∧
      q.position.board.get (!P.side) = P.target.position.board.get (!P.side) :=
  P.toPreparedLeaf.fire hHN hinc hlast

#print axioms fire

end PreparedBody

end Erdos591.Positive.Game.Relay
