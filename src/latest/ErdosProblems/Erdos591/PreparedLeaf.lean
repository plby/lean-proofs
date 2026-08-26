import ErdosProblems.Erdos591.CompletedOther

/-!
# A prepared upper response through the last selection of any lower body

The replay only uses the retained same-body execution and the last-first
overlap of the body labels. Later selected root bodies may still exist.
The last-body construction adds its separate root-exhaustion invariant.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

structure PreparedLeaf (N H : Set ℕ) (blue : SimpleGraph G)
    (b : Concrete.Hist N → ℕ) (σ : (exactGame N blue).ArchitectStrategy) (w : LabeledWord) where
  target : Concrete.Hist N
  side : Bool
  stem : LabeledWord
  remainingBodies : ℕ
  budget : ℕ
  lowerSize : ℕ
  upperSize : ℕ
  labels : LastFirstLabels H budget lowerSize upperSize
  targetPending : target.position.pending = some ⟨side, .advance upperSize⟩
  targetMarker : (target.position.board.get side).markerEvent = true
  targetBound : max target.position.bound (b target) ≤ budget
  targetWinning : (exactGame N blue).ArchitectWins H b σ target
  stemSame : LabeledWord.SameStructure stem (target.position.board.get side)
  stemParser : stem.parser = .blocks (remainingBodies + 1)
  first : LabeledWord
  firstRead : stem.read labels.lower labels.marker = some first
  atoms : List (Finset ℕ × ℕ)
  run : LabeledWord.LegalRun first atoms w
  bodyLabels_eq : w.bodyLabels = first.bodyLabels
  pool : ∀ a ∈ atoms, a.2 ∈ H ∧ budget < a.2
  upto : LabeledWord.UpToLeaf labels.pivot w

namespace PreparedLeaf

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy} {w v : LabeledWord}

theorem first_eq (P : PreparedLeaf N H blue b σ w) :
    P.first = P.stem.record P.labels.lower P.labels.marker
      (Parser.normalize P.remainingBodies P.labels.marker) := by
  exact Option.some.inj (P.firstRead.symm.trans (by
    simp [LabeledWord.read, P.stemParser, Parser.step]))

theorem first_leaf (P : PreparedLeaf N H blue b σ w) : P.first.leafIndex = 0 := by
  simp [P.first_eq, LabeledWord.record, P.stemParser]

theorem currentLabel (P : PreparedLeaf N H blue b σ w) : w.currentLabel = P.labels.lower := by
  simp [LabeledWord.currentLabel, P.bodyLabels_eq, P.first_eq, LabeledWord.record, P.stemParser]

theorem rootLabel (P : PreparedLeaf N H blue b σ w) : w.rootLabel = P.stem.rootLabel :=
  (P.run.rootLabel_eq (LabeledWord.read_parser_ne_start P.firstRead)).trans
    (LabeledWord.read_rootLabel_eq P.firstRead (by simp [P.stemParser]))

theorem body_length (P : PreparedLeaf N H blue b σ w) :
    w.bodyLabels.length = P.stem.bodyLabels.length + 1 := by
  simp [P.bodyLabels_eq, P.first_eq, LabeledWord.record, P.stemParser]

def move (P : PreparedLeaf N H blue b σ w) {ys : List (Finset ℕ × ℕ)}
    (h : LabeledWord.LegalRun w ys v) (hbody : v.bodyLabels = w.bodyLabels)
    (hpool : ∀ a ∈ ys, a.2 ∈ H ∧ P.budget < a.2)
    (hup : LabeledWord.UpToLeaf P.labels.pivot v) : PreparedLeaf N H blue b σ v where
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
  upto := hup

theorem fire_full (P : PreparedLeaf N H blue b σ w) (hHN : H ⊆ N)
    (hinc : w.coordinates.Pairwise (· < ·)) (hlast : w.leafIndex = P.labels.pivot) :
    ∃ q, (exactGame N blue).FollowStep σ H b P.target q ∧ q.position.pending = none ∧
      (q.position.board.get P.side).coordinates = w.coordinates ∧
      (q.position.board.get P.side).relaxed = true ∧
      q.position.board.get (!P.side) = P.target.position.board.get (!P.side) ∧
      (q.position.board.get P.side).rootLabel = (P.target.position.board.get P.side).rootLabel ∧
      (q.position.board.get P.side).bodyLabels =
        (P.target.position.board.get P.side).bodyLabels ++ [P.labels.upper] ∧
      (q.position.board.get P.side).leafIndex = P.labels.pivot := by
  let xs := P.atoms.map Prod.snd
  have hcount := P.run.leafIndex_of_body_length
    (LabeledWord.read_parser_ne_start P.firstRead) (congrArg List.length P.bodyLabels_eq)
  have hlength : xs.length = P.labels.pivot := by
    simp only [P.first_leaf, Nat.zero_add, hlast] at hcount
    simpa [xs] using hcount.symm
  have hcoords : w.coordinates = P.stem.coordinates ++ P.labels.marker :: xs := by
    rw [LabeledWord.runAtoms_coordinates P.run.run, (LabeledWord.read_spec P.firstRead).2]
    simp [xs, List.append_assoc]
  have htailInc : (P.labels.marker :: xs).Pairwise (· < ·) := by
    rw [hcoords] at hinc
    exact (List.pairwise_append.mp hinc).2.1
  have hxsPool : ∀ x ∈ xs, x ∈ H := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact (P.pool a ha).1
  have hparser : (P.target.position.board.get P.side).parser =
      .blocks (P.remainingBodies + 1) := P.stemSame.parser_eq.symm.trans P.stemParser
  obtain ⟨u, hr, _hsort, huH, huB⟩ := P.labels.leaf_reply P.target.position.board P.side
    P.remainingBodies xs ((Position.history_dataInvariant P.target).2.1 P.side).1
    hparser P.targetMarker hlength htailInc hxsPool
  obtain ⟨q, hstep, hboard, hnone⟩ := Concrete.follow_reply hHN (payoff blue) σ P.target
    P.targetPending hr huH (fun x hx =>
      ⟨((le_max_left _ _).trans P.targetBound).trans_lt (huB x hx),
        ((le_max_right _ _).trans P.targetBound).trans_lt (huB x hx)⟩)
  have hword : q.position.board.get P.side =
      LabeledWord.bodyLeafCursor (P.target.position.board.get P.side)
        P.labels.upper P.labels.marker P.remainingBodies xs := by simp [hboard]
  have hsame : (q.position.board.get P.side).coordinates = w.coordinates := by
    rw [hword, hcoords]
    simp [LabeledWord.bodyLeafCursor, P.stemSame.coordinates_eq]
  have hrel : (q.position.board.get P.side).relaxed = true := by
    rw [hword]
    simpa [LabeledWord.relaxed, LabeledWord.bodyLeafCursor, LabeledWord.currentLabel, hlength] using
      (show 0 < P.labels.pivot ∧ (P.target.position.board.get P.side).bodyLabels.length + 1 ∈
          (P.target.position.board.get P.side).rootLabel ∧ P.labels.pivot ∈ P.labels.upper from
        ⟨(P.labels.label_bounds.2 P.labels.pivot P.labels.pivot_upper).1,
          LabeledWord.marker_body_mem P.targetMarker, P.labels.pivot_upper⟩)
  refine ⟨q, hstep, hnone, hsame, hrel, by simpa [hboard] using hr.other_eq, ?_, ?_, ?_⟩
  · simp [hword, LabeledWord.bodyLeafCursor]
  · simp [hword, LabeledWord.bodyLeafCursor]
  · simp [hword, LabeledWord.bodyLeafCursor, hlength]

theorem fire (P : PreparedLeaf N H blue b σ w) (hHN : H ⊆ N)
    (hinc : w.coordinates.Pairwise (· < ·)) (hlast : w.leafIndex = P.labels.pivot) :
    ∃ q, (exactGame N blue).FollowStep σ H b P.target q ∧ q.position.pending = none ∧
      (q.position.board.get P.side).coordinates = w.coordinates ∧
      (q.position.board.get P.side).relaxed = true ∧
      q.position.board.get (!P.side) = P.target.position.board.get (!P.side) := by
  obtain ⟨q, hs, hn, hc, hr, ho, _hroot, _hbody, _hleaf⟩ := P.fire_full hHN hinc hlast
  exact ⟨q, hs, hn, hc, hr, ho⟩

#print axioms fire_full
#print axioms fire

end PreparedLeaf

end Erdos591.Positive.Game.Relay
