import ErdosProblems.Erdos591.NextLeafResponse
import ErdosProblems.Erdos591.SharedTailHistory

/-!
# Replaying a fine prefix as a delayed next-selected-leaf response

The two labelings may differ, but the starting structural cursor is
shared. The fine continuation stays in its current body and reaches the
next coarse selected index. Erasing its new labels preserves the old
coarse labels and produces an actual advance response, not merely a raw
coordinate execution.
-/

namespace Erdos591.Positive.Game

theorem LabeledWord.SameStructure.next_leaf_reply {board : Board} {side : Bool}
    {f v : LabeledWord} {as : List (Finset ℕ × ℕ)} {j : ℕ}
    (h : LabeledWord.SameStructure (board.get side) f)
    (hw : (board.get side).CursorInvariant)
    (hs : LabeledWord.UpToLeaf j (board.get side)) (hlt : (board.get side).leafIndex < j)
    (hnext : ∀ k ∈ (board.get side).currentLabel, (board.get side).leafIndex < k → j ≤ k)
    (hr : f.runAtoms as = some v) (hleaf : v.leafIndex = j)
    (hcount : v.bodyLabels.length = f.bodyLabels.length) (hmarker : v.bodyMarker = f.bodyMarker)
    (hinc : (as.map Prod.snd).Pairwise (· < ·)) :
    ∃ z, Reply board ⟨side, .advance 0⟩ (as.map Prod.snd).toFinset (board.update side z) ∧
      LabeledWord.SameStructure z v ∧ z.relaxed = true ∧
      z.bodyLabels = (board.get side).bodyLabels := by
  obtain ⟨z, hz, hshape⟩ := h.erase_run hr
  have hlegal := LabeledWord.legal_of_zero_atoms hz
  obtain ⟨r, k, hparse⟩ := hs.parser_leaves hw
  have hstart : (board.get side).parser ≠ .start := by simp [hparse]
  have hlength : z.bodyLabels.length = (board.get side).bodyLabels.length :=
    hshape.body_length.trans (hcount.trans h.body_length.symm)
  have hlabels : z.bodyLabels = (board.get side).bodyLabels := by
    obtain ⟨tail, heq⟩ := hlegal.bodyLabels_prefix hstart
    have htlen : tail.length = 0 := by
      have he := congrArg List.length heq
      simp only [List.length_append] at he
      omega
    simpa only [List.length_eq_zero_iff.mp htlen, List.append_nil] using heq.symm
  have hbody : z.bodyMarker = (board.get side).bodyMarker :=
    hshape.bodyMarker_eq.trans (hmarker.trans h.bodyMarker_eq.symm)
  have hroot := hlegal.rootLabel_eq hstart
  have hidx := hshape.leaf_eq.trans hleaf
  have hzs : LabeledWord.UpToLeaf j z := by
    constructor
    · simpa [hlabels, hroot] using hs.selected
    · simpa [LabeledWord.currentLabel, hlabels] using hs.mem
    · exact hidx.le
  have hreply := Reply.next_leaf_of_list board side hw hs hlt hnext hz hzs hidx hlabels hbody hinc
  exact ⟨z, hreply, hshape, hzs.relaxed_of_eq (hlegal.cursorInvariant hw) hidx, hlabels⟩

namespace Concrete

theorem follow_next_leaf {N H : Set ℕ} (hHN : H ⊆ N) (payoff : Bool → Board → Bool)
    {b : Hist N → ℕ} (σ : (game N payoff).ArchitectStrategy) (p : Hist N) (side : Bool)
    (hp : p.position.pending = some ⟨side, .advance 0⟩)
    {f v : LabeledWord} {as : List (Finset ℕ × ℕ)} {j : ℕ}
    (hsame : LabeledWord.SameStructure (p.position.board.get side) f)
    (hs : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hlt : (p.position.board.get side).leafIndex < j)
    (hnext : ∀ k ∈ (p.position.board.get side).currentLabel,
      (p.position.board.get side).leafIndex < k → j ≤ k)
    (hr : f.runAtoms as = some v) (hleaf : v.leafIndex = j)
    (hcount : v.bodyLabels.length = f.bodyLabels.length) (hmarker : v.bodyMarker = f.bodyMarker)
    (hinc : (as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ a ∈ as, a.2 ∈ H ∧ p.position.bound < a.2 ∧ b p < a.2) :
    ∃ q, (game N payoff).FollowStep σ H b p q ∧ q.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get side) v ∧
      (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      q.position.board.get (!side) = p.position.board.get (!side) := by
  obtain ⟨z, hreply, hshape, hrel, hlabels⟩ := hsame.next_leaf_reply
    ((Position.history_dataInvariant p).2.1 side).1 hs hlt hnext hr hleaf hcount hmarker hinc
  have hvalues : ∀ x ∈ (as.map Prod.snd).toFinset,
      x ∈ H ∧ p.position.bound < x ∧ b p < x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hpool a ha
  obtain ⟨q, hstep, hboard, hnone⟩ := follow_reply hHN payoff σ p hp hreply
    (fun x hx => (hvalues x hx).1) (fun x hx => (hvalues x hx).2)
  exact ⟨q, hstep, hnone, by simpa [hboard] using hshape,
    by simpa [hboard] using hrel, by simpa [hboard] using hlabels,
    by simpa [hboard] using hreply.other_eq⟩

#print axioms follow_next_leaf

end Concrete

end Erdos591.Positive.Game
