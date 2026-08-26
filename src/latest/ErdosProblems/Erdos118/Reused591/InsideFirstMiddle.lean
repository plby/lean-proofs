import ErdosProblems.Erdos118.Reused591.InsideMiddleStart
import ErdosProblems.Erdos118.Reused591.InsideMiddleReplay
import ErdosProblems.Erdos118.Reused591.BodyPrefixExtension

namespace Erdos118.Reused591

/-!
# The first middle phase from an actual last-body request

Install the lower common-last body label, exhaust its nonlast leaves,
and replay the opposite last leaf as the upper play's next leaf.
The first response's exact literal prefix and every subsequent input
run remain available for the still-unsubmitted second lower response.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_first_middle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (p upper : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true) {B a c : ℕ} (L : LastLastLabels H B a c)
    (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hroot : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hB : max p.position.bound (b p) ≤ B)
    (hrelOther : p.position.board.right.relaxed = true)
    (hrootOther : ∀ i ∈ p.position.board.right.rootLabel,
      i ≤ p.position.board.right.bodyLabels.length)
    (hpUpper : upper.position.pending = some ⟨false, .advance 0⟩)
    (hsame : LabeledWord.SameStructure upper.position.board.left p.position.board.right)
    (hup : LabeledWord.UpToLeaf (p.position.board.right.currentLabel.sup id)
      upper.position.board.left)
    (hstrict : upper.position.board.left.leafIndex < p.position.board.right.currentLabel.sup id)
    (hnext : ∀ i ∈ upper.position.board.left.currentLabel,
      upper.position.board.left.leafIndex < i → p.position.board.right.currentLabel.sup id ≤ i)
    (hUpperB : max upper.position.bound (b upper) ≤ B)
    {t mode : Bool} {other : LabeledWord} (upperOrigin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other p.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target) :
    ∃ q v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      (exactGame N blue).FollowStep σ H b upper v ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧ v.position.pending = none ∧
      q.position.board.left.relaxed = true ∧ q.position.board.left.leafIndex = L.penultimate ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [L.lower] ∧
      q.position.board.left.bodyMarker = L.marker ∧
      q.position.board.right.relaxed = true ∧ ¬ Macro.Pending q.position.board.right ∧
      q.position.board.right.bodyLabels = p.position.board.right.bodyLabels ∧
      q.position.board.right.bodyMarker = p.position.board.right.bodyMarker ∧
      q.position.board.right.leafIndex = p.position.board.right.currentLabel.sup id ∧
      LabeledWord.SameStructure v.position.board.left q.position.board.right ∧
      v.position.board.left.relaxed = true ∧ v.position.board.right = upper.position.board.right ∧
      ∃ first r xs, (exactGame N blue).FollowStep σ H b p first ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) first q ∧
        p.position.board.left.parser = .blocks (r + 1) ∧
        first.position.board.left =
          LabeledWord.bodyLeafCursor p.position.board.left L.lower L.marker r xs ∧
        first.position.board.right = p.position.board.right ∧ B < first.position.bound ∧
        xs.length = L.firstLower ∧ (L.marker :: xs).Pairwise (· < ·) ∧
        (∀ x ∈ xs, x ∈ H ∧ L.marker < x) ∧
        (∀ s, ∃ as, LabeledWord.LegalRun (first.position.board.get s) as
          (q.position.board.get s) ∧ ∀ atom ∈ as, atom.2 ∈ H ∧ first.position.bound < atom.2) := by
  obtain ⟨first, hstep, hnone, _hrel, htarget, hpivot, hleaves, hrootFirst, hlabelsFirst,
      hmarkerFirst, hother, hsep, hboundFirst, r, xs, hparse, hword, hlen, hinc, hpool⟩ :=
    inside_middle_start hHN hH blue σ p L hp hm hroot hB
  have hMfirst : ∃ M : Managed N H blue b σ t mode other first.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target := by
    rw [hother]
    exact hmanaged
  obtain ⟨q, v, hmid, huv, hpq, hnv, hqr, hqi, hqb, hqm, hqOther, hqLast,
      hqBodyOther, hqMarkerOther, hqLeafOther, hshape, hvr, hvo, hinputs, _Mq, _hMq⟩ :=
    inside_middle_opposite_replay hHN hH blue first upper
      (hwin.of_reachable (exactGame N blue) (.single hstep))
      (follow_mode_some (.single hstep) hmode) hnone hsep htarget L.penultimate_lt_pivot
      hpivot hleaves hrootFirst (by simpa only [hother] using hrelOther)
      (by simpa only [hother] using hrootOther) false hpUpper
      (by simpa only [hother, Board.get] using hsame)
      (by simpa only [hother, Board.get] using hup)
      (by simpa only [hother, Board.get] using hstrict)
      (by simpa only [hother, Board.get] using hnext)
      (hUpperB.trans hboundFirst.le) upperOrigin hMfirst
  exact ⟨q, v, hmid.head hstep, huv, hpq, hnv, hqr, hqi, hqb.trans hlabelsFirst,
    hqm.trans hmarkerFirst, hqOther, hqLast,
    by simpa only [hother] using hqBodyOther, by simpa only [hother] using hqMarkerOther,
    by simpa only [hother] using hqLeafOther, hshape, hvr, hvo,
    first, r, xs, hstep, hmid, hparse, hword, hother, hboundFirst, hlen, hinc, hpool, hinputs⟩

#print axioms inside_first_middle

theorem first_middle_prefix {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p first q : Concrete.Hist N) {B a c r : ℕ} (L : LastLastLabels H B a c)
    (xs : List ℕ) (hparse : p.position.board.left.parser = .blocks (r + 1))
    (hword : first.position.board.left =
      LabeledWord.bodyLeafCursor p.position.board.left L.lower L.marker r xs)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) first q)
    (hlabels : q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [L.lower])
    (hidx : q.position.board.left.leafIndex = L.penultimate)
    (hxs : ∀ x ∈ xs, x ∈ H) :
    ∃ full, full.length = L.penultimate ∧ (L.marker :: full).Pairwise (· < ·) ∧
      (∀ x ∈ full, x ∈ H) ∧
      LabeledWord.SameStructure q.position.board.left
        (LabeledWord.bodyLeafCursor p.position.board.left L.lower L.marker r full) := by
  obtain ⟨as, has, hpool⟩ := follow_word_inputs_above_bound hpath false
  have hrun : LabeledWord.LegalRun
      (LabeledWord.bodyLeafCursor p.position.board.left L.lower L.marker r xs)
      as q.position.board.left := by simpa only [Board.get, hword] using has
  obtain ⟨hlen, hcoords, hshape⟩ := hrun.bodyLeafCursor_prefix hparse
    (by simp [hlabels]) (by rw [hidx]; exact (L.lower_fresh _ L.penultimate_lower).2.2.le)
  have hinc : (L.marker :: (xs ++ as.map Prod.snd)).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant q).2.1 false).2
    change q.position.board.left.coordinates.Pairwise (· < ·) at hi
    rw [hcoords] at hi
    exact (List.pairwise_append.mp hi).2.1
  refine ⟨xs ++ as.map Prod.snd, hlen.trans hidx, hinc, ?_, hshape⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hxs x hx
  · obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hx
    exact (hpool atom ha).1

#print axioms first_middle_prefix

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
