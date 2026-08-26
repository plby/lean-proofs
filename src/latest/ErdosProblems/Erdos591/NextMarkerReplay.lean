import ErdosProblems.Erdos591.NextMarkerResponse
import ErdosProblems.Erdos591.SharedTailHistory

/-!
# Replaying a fine continuation as the next coarse body-marker response

The coarse current body has no unread selected leaf. Its next selected
root index is the fine endpoint marker. Empty labels on new coordinates
retain the old coarse labels and produce exactly the pending response.
-/

namespace Erdos591.Positive.Game

theorem LabeledWord.SameStructure.next_marker_reply {board : Board} {side : Bool}
    {f v : LabeledWord} {as : List (Finset ℕ × ℕ)} {i : ℕ}
    (h : LabeledWord.SameStructure (board.get side) f)
    (hw : (board.get side).CursorInvariant) (hrel : (board.get side).relaxed = true)
    (hn : (board.get side).NoLeafPending) (hs : LabeledWord.BeforeBody i (board.get side))
    (hnext : ∀ k ∈ (board.get side).rootLabel, (board.get side).bodyLabels.length < k → i ≤ k)
    (hr : f.runAtoms as = some v) (hm : v.markerEvent = true)
    (hindex : v.bodyLabels.length + 1 = i) (hinc : (as.map Prod.snd).Pairwise (· < ·)) :
    ∃ z, Reply board ⟨side, .advance 0⟩ (as.map Prod.snd).toFinset (board.update side z) ∧
      LabeledWord.SameStructure z v ∧ z.markerEvent = true ∧ z.bodyLabels.length + 1 = i := by
  obtain ⟨z, hz, hshape⟩ := h.erase_run hr
  have hlegal := LabeledWord.legal_of_zero_atoms hz
  have hstart := LabeledWord.relaxed_ne_start hw hrel
  have hroot := hlegal.rootLabel_eq hstart
  have hidx : z.bodyLabels.length + 1 = i := by rw [hshape.body_length]; exact hindex
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
  have hzmarker : z.markerEvent = true := by
    simp [LabeledWord.markerEvent, hshape.parser_eq, hparse, hidx, hroot, hs.1]
  have hreply := Reply.next_marker_of_list board side hw hrel hn hs hnext hz hzmarker hidx hinc
  exact ⟨z, hreply, hshape, hzmarker, hidx⟩

namespace Concrete

theorem follow_next_marker {N H : Set ℕ} (hHN : H ⊆ N) (payoff : Bool → Board → Bool)
    {b : Hist N → ℕ} (σ : (game N payoff).ArchitectStrategy) (p : Hist N) (side : Bool)
    (hp : p.position.pending = some ⟨side, .advance 0⟩)
    {f v : LabeledWord} {as : List (Finset ℕ × ℕ)} {i : ℕ}
    (hsame : LabeledWord.SameStructure (p.position.board.get side) f)
    (hrel : (p.position.board.get side).relaxed = true)
    (hn : (p.position.board.get side).NoLeafPending)
    (hs : LabeledWord.BeforeBody i (p.position.board.get side))
    (hnext : ∀ k ∈ (p.position.board.get side).rootLabel,
      (p.position.board.get side).bodyLabels.length < k → i ≤ k)
    (hr : f.runAtoms as = some v) (hm : v.markerEvent = true)
    (hindex : v.bodyLabels.length + 1 = i) (hinc : (as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ a ∈ as, a.2 ∈ H ∧ p.position.bound < a.2 ∧ b p < a.2) :
    ∃ q, (game N payoff).FollowStep σ H b p q ∧ q.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get side) v ∧
      (q.position.board.get side).markerEvent = true ∧
      (q.position.board.get side).bodyLabels.length + 1 = i ∧
      q.position.board.get (!side) = p.position.board.get (!side) := by
  obtain ⟨z, hreply, hshape, hmarker, hidx⟩ := hsame.next_marker_reply
    ((Position.history_dataInvariant p).2.1 side).1 hrel hn hs hnext hr hm hindex hinc
  have hvalues : ∀ x ∈ (as.map Prod.snd).toFinset,
      x ∈ H ∧ p.position.bound < x ∧ b p < x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hpool a ha
  obtain ⟨q, hstep, hboard, hnone⟩ := follow_reply hHN payoff σ p hp hreply
    (fun x hx => (hvalues x hx).1) (fun x hx => (hvalues x hx).2)
  exact ⟨q, hstep, hnone, by simpa [hboard] using hshape,
    by simpa [hboard] using hmarker, by simpa [hboard] using hidx,
    by simpa [hboard] using hreply.other_eq⟩

#print axioms follow_next_marker

end Concrete

end Erdos591.Positive.Game
