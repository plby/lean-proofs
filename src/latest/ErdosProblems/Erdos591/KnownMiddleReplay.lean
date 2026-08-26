import ErdosProblems.Erdos591.KnownMiddleEndpoint
import ErdosProblems.Erdos591.NextLeafReplay

/-!
# Replay the fixed-label middle endpoint above all waiting bounds

Restrict new lower inputs to a fresh tail before following the middle
phase. Both coordinate prefixes retain that bound. The opposite last
leaf is exactly the upper play's pending next leaf.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem known_middle_opposite_replay {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p upper : Concrete.Hist N) (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true) {k j : ℕ}
    (hk : LabeledWord.UpToLeaf k p.position.board.left) (hkj : k < j)
    (hj : j ∈ p.position.board.left.currentLabel)
    (hleaves : ∀ i ∈ p.position.board.left.currentLabel, i = j ∨ i ≤ k)
    (hrootS : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    (hrelT : p.position.board.right.relaxed = true)
    (hrootT : ∀ i ∈ p.position.board.right.rootLabel, i ≤ p.position.board.right.bodyLabels.length)
    (hentry : p.position.board.left.leafIndex < k ∨ (p.position.pending = none ∧
      ∀ y ∈ p.position.board.right.coordinates, y ≤ p.position.board.left.coordinates.getLastD 0))
    (side : Bool) (hpUpper : upper.position.pending = some ⟨side, .advance 0⟩)
    (hsame : LabeledWord.SameStructure (upper.position.board.get side) p.position.board.right)
    (hup : LabeledWord.UpToLeaf (p.position.board.right.currentLabel.sup id)
      (upper.position.board.get side))
    (hstrict : (upper.position.board.get side).leafIndex <
      p.position.board.right.currentLabel.sup id)
    (hnext : ∀ i ∈ (upper.position.board.get side).currentLabel,
      (upper.position.board.get side).leafIndex < i →
        p.position.board.right.currentLabel.sup id ≤ i)
    (B : ℕ) (hB : max upper.position.bound (b upper) ≤ B) :
    ∃ q v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      (exactGame N blue).FollowStep σ H b upper v ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧ v.position.pending = none ∧
      q.position.board.left.relaxed = true ∧ q.position.board.left.leafIndex = k ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ∧
      q.position.board.left.bodyMarker = p.position.board.left.bodyMarker ∧
      q.position.board.right.relaxed = true ∧ ¬ Macro.Pending q.position.board.right ∧
      q.position.board.right.bodyLabels = p.position.board.right.bodyLabels ∧
      q.position.board.right.bodyMarker = p.position.board.right.bodyMarker ∧
      q.position.board.right.leafIndex = p.position.board.right.currentLabel.sup id ∧
      LabeledWord.SameStructure (v.position.board.get side) q.position.board.right ∧
      (v.position.board.get side).relaxed = true ∧
      v.position.board.get (!side) = upper.position.board.get (!side) ∧
      ∀ s, ∃ as, LabeledWord.LegalRun (p.position.board.get s) as (q.position.board.get s) ∧
        ∀ atom ∈ as, atom.2 ∈ H ∧ B < atom.2 := by
  let J := H \ Set.Iic B
  have hJH : J ⊆ H := fun _ hx => hx.1
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic B)
  have hJfresh : ∀ x ∈ J, B < x := fun _ hx => lt_of_not_ge hx.2
  obtain ⟨q, hpq, hqp, hqr, hqi, hqb, hqm, hqTr, hqLast, hqTb, hqTm, hqTi⟩ :=
    known_middle_endpoint (hJH.trans hHN) hJ blue
      (hwin.mono (exactGame N blue) hJH (fun _ => le_rfl)) hmode hk hkj hj hleaves
        hrootS hrelT hrootT hentry
  have hinputs : ∀ s, ∃ as,
      LabeledWord.LegalRun (p.position.board.get s) as (q.position.board.get s) ∧
        ∀ atom ∈ as, atom.2 ∈ H ∧ B < atom.2 := by
    intro s
    obtain ⟨as, has, hpool⟩ := follow_word_inputs hpq 0 (fun _ => Nat.zero_le _) s
    exact ⟨as, has, fun atom hatom =>
      ⟨hJH (hpool atom hatom).1, hJfresh atom.2 (hpool atom hatom).1⟩⟩
  obtain ⟨as, has, hpool⟩ := hinputs true
  have hinc : (as.map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant q).2.1 true).2
    rw [LabeledWord.runAtoms_coordinates has.run] at hi
    exact (List.pairwise_append.mp hi).2.1
  obtain ⟨v, huv, hvn, hshape, hvr, _hvb, hother⟩ := Concrete.follow_next_leaf hHN (payoff blue)
    σ upper side hpUpper hsame hup hstrict hnext has.run hqTi (congrArg List.length hqTb)
      hqTm hinc (fun atom hatom =>
        ⟨(hpool atom hatom).1, ((le_max_left _ _).trans hB).trans_lt (hpool atom hatom).2,
          ((le_max_right _ _).trans hB).trans_lt (hpool atom hatom).2⟩)
  have hpqH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hpq
  exact ⟨q, v, hpqH, huv, hqp, hvn, hqr, hqi, hqb, hqm, hqTr, hqLast,
    hqTb, hqTm, hqTi, hshape, hvr, hother, hinputs⟩

#print axioms known_middle_opposite_replay

end Erdos591.Positive.Game.Payoff
