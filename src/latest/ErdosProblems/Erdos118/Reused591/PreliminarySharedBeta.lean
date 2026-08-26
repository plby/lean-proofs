import ErdosProblems.Erdos118.Reused591.PreliminaryPivotLabels
import ErdosProblems.Erdos118.Reused591.SharedNextLeaf
import ErdosProblems.Erdos118.Reused591.FreshLeafNextMarker

namespace Erdos118.Reused591

/-!
# The actual shared beta after the two preliminary lower phases

Read beta in SU and replay its retained full S prefix in ST. Both
opposite words stay fixed, then their next selected continuations are
requested. Their new bounds are therefore fixed before the upper bridge.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_shared_beta {N H HL : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (old fine : Concrete.Hist N) {B P Q r t : ℕ}
    (L : PreliminaryPivotLabels HL B P Q r t)
    (hwinOld : (exactGame N blue).ArchitectWins H b σ old)
    (hwinFine : (exactGame N blue).ArchitectWins H b σ fine)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hpFine : fine.position.pending = some ⟨false, .advance 0⟩)
    (hrOld : old.position.board.left.relaxed = true)
    (hrFine : fine.position.board.left.relaxed = true)
    (hlOld : old.position.board.left.currentLabel = L.lower)
    (hlFine : fine.position.board.left.currentLabel = L.upper)
    (hbOld : old.position.board.left.leafIndex < L.beta)
    (hbFine : fine.position.board.left.leafIndex < L.beta)
    (hnOld : ∀ x ∈ L.lower, old.position.board.left.leafIndex < x → L.beta ≤ x)
    (hnFine : ∀ x ∈ L.upper, fine.position.board.left.leafIndex < x → L.beta ≤ x)
    (hTrel : old.position.board.right.relaxed = true)
    (hUrel : fine.position.board.right.relaxed = true)
    (hTpending : Macro.Pending old.position.board.right)
    (hUpending : Macro.Pending fine.position.board.right)
    {anchor : LabeledWord} {front : List (Finset ℕ × ℕ)}
    (hshape : LabeledWord.SameStructure old.position.board.left anchor)
    (hfront : LabeledWord.LegalRun anchor front fine.position.board.left)
    (hpool : ∀ atom ∈ front, atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2)
    (hcount : fine.position.board.left.bodyLabels.length = anchor.bodyLabels.length)
    (hmarker : fine.position.board.left.bodyMarker = anchor.bodyMarker) :
    ∃ st su, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old st ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine su ∧
      st.position.pending = some ⟨true, .advance 0⟩ ∧
      su.position.pending = some ⟨true, .advance 0⟩ ∧
      LabeledWord.SameStructure st.position.board.left su.position.board.left ∧
      st.position.board.left.relaxed = true ∧ su.position.board.left.relaxed = true ∧
      st.position.board.left.currentLabel = L.lower ∧
      su.position.board.left.currentLabel = L.upper ∧
      st.position.board.left.leafIndex = L.beta ∧ su.position.board.left.leafIndex = L.beta ∧
      st.position.board.left.bodyLabels = old.position.board.left.bodyLabels ∧
      su.position.board.left.bodyLabels = fine.position.board.left.bodyLabels ∧
      st.position.board.right = old.position.board.right ∧
      su.position.board.right = fine.position.board.right ∧
      (∀ x ∈ st.position.board.right.coordinates,
        x ≤ st.position.board.left.coordinates.getLastD 0) ∧
      (∀ x ∈ su.position.board.right.coordinates,
        x ≤ su.position.board.left.coordinates.getLastD 0) := by
  have hupOld : LabeledWord.UpToLeaf L.beta old.position.board.left :=
    ⟨(of_decide_eq_true hrOld).2.1, hlOld ▸ L.beta_lower, hbOld.le⟩
  have hupFine : LabeledWord.UpToLeaf L.beta fine.position.board.left :=
    ⟨(of_decide_eq_true hrFine).2.1, hlFine ▸ L.beta_upper, hbFine.le⟩
  obtain ⟨v, w, hOldV, hFineW, _hvn, _hwn, hSshape, hvrel, hwrel, hvi, hwi,
      hvl, hwl, hvother, hwother⟩ := shared_next_leaf_from_prefix hHN hH blue σ old fine
        false false hpOld hpFine hupOld hbOld (by simpa only [Board.get, hlOld] using hnOld)
        hupFine hbFine (by simpa only [Board.get, hlFine] using hnFine)
        hshape hfront hpool hcount hmarker
  simp only [Board.get, Bool.not_false] at hSshape hvrel hwrel hvi hwi hvl hwl hvother hwother
  have hvsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hOldV).reply_separation hpOld
  have hwsep :=
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hFineW).reply_separation hpFine
  obtain ⟨st, hvst, hstBoard, hstp⟩ := winning_next_selection_after_fresh_leaf hHN hH blue
    (hwinOld.of_reachable (exactGame N blue) (.single hOldV)) false hvrel hvsep
    (by simpa only [Board.get, Bool.not_false, hvother] using hTrel)
    (by simpa only [Board.get, Bool.not_false, hvother] using hTpending)
  obtain ⟨su, hwsu, hsuBoard, hsup⟩ := winning_next_selection_after_fresh_leaf hHN hH blue
    (hwinFine.of_reachable (exactGame N blue) (.single hFineW)) false hwrel hwsep
    (by simpa only [Board.get, Bool.not_false, hwother] using hUrel)
    (by simpa only [Board.get, Bool.not_false, hwother] using hUpending)
  refine ⟨st, su, (Relation.ReflTransGen.single hOldV).trans hvst,
    (Relation.ReflTransGen.single hFineW).trans hwsu, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Bool.not_false] using hstp
  · simpa only [Bool.not_false] using hsup
  · simpa only [hstBoard, hsuBoard] using hSshape
  · simpa only [hstBoard] using hvrel
  · simpa only [hsuBoard] using hwrel
  · simpa only [hstBoard, LabeledWord.currentLabel, hvl] using hlOld
  · simpa only [hsuBoard, LabeledWord.currentLabel, hwl] using hlFine
  · simpa only [hstBoard] using hvi
  · simpa only [hsuBoard] using hwi
  · simpa only [hstBoard] using hvl
  · simpa only [hsuBoard] using hwl
  · simpa only [hstBoard] using hvother
  · simpa only [hsuBoard] using hwother
  · simpa only [hstBoard, Board.get, Bool.not_false] using hvsep
  · simpa only [hsuBoard, Board.get, Bool.not_false] using hwsep

#print axioms preliminary_shared_beta

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
