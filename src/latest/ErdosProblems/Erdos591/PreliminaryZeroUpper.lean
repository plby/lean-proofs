import ErdosProblems.Erdos591.DeferredBodyFirst
import ErdosProblems.Erdos591.PreliminaryPivotRanks
import ErdosProblems.Erdos591.FreshLeafNextMarker

/-!
# Share beta directly when the second preliminary group is empty

The upper S minimum is beta. Complete its pending body reply from the
retained first-phase prefix, and replay just the new tail as the old
ST beta response. No extra lower U selected leaf is consumed before beta.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_zero_upper {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (old fine : Concrete.Hist N) {B P Q r k : ℕ}
    (L : PreliminaryPivotLabels H B P Q r 0)
    (hwinOld : (exactGame N blue).ArchitectWins H b σ old)
    (hwinFine : (exactGame N blue).ArchitectWins H b σ fine)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hpFine : fine.position.pending = some ⟨false, .advance Q⟩)
    (hrOld : old.position.board.left.relaxed = true)
    (hlOld : old.position.board.left.currentLabel = L.lower)
    (hbOld : old.position.board.left.leafIndex < L.beta)
    (hnOld : ∀ x ∈ L.lower, old.position.board.left.leafIndex < x → L.beta ≤ x)
    (hmFine : fine.position.board.left.markerEvent = true)
    (hparse : fine.position.board.left.parser = .blocks (k + 1))
    (hB : max fine.position.bound (b fine) ≤ B)
    (hTrel : old.position.board.right.relaxed = true)
    (hUrel : fine.position.board.right.relaxed = true)
    (hTpending : Macro.Pending old.position.board.right)
    (hUpending : Macro.Pending fine.position.board.right)
    (xs : List ℕ) (hinc : (L.marker :: xs).Pairwise (· < ·))
    (hpool : ∀ x ∈ xs, x ∈ H)
    (hshape : LabeledWord.SameStructure old.position.board.left
      (LabeledWord.bodyLeafCursor fine.position.board.left L.upper L.marker k xs)) :
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
      su.position.board.left.bodyLabels = fine.position.board.left.bodyLabels ++ [L.upper] ∧
      st.position.board.right = old.position.board.right ∧
      su.position.board.right = fine.position.board.right ∧
      (∀ x ∈ st.position.board.right.coordinates,
        x ≤ st.position.board.left.coordinates.getLastD 0) ∧
      (∀ x ∈ su.position.board.right.coordinates,
        x ≤ su.position.board.left.coordinates.getLastD 0) := by
  have hH := hK.mono hKH
  have hbefore : xs.length < L.upper.min' ⟨_, L.beta_upper⟩ := by
    rw [L.upper_min_of_zero]
    have hi : old.position.board.left.leafIndex = xs.length := hshape.leaf_eq
    omega
  obtain ⟨w, ys, hFineW, _hwn, hwrel, _hwroot, hwlabels, hwcurrent, hwi, hwmarker,
      hwother, hwsep, _hword, htail, _hlen, hfullInc, hys⟩ :=
    deferred_body_first_from_prefix hHN hKH hK blue σ fine false L.upper ⟨_, L.beta_upper⟩
      L.upper_card L.upper_fresh L.marker_fresh hpFine hmFine hparse hB xs hinc hpool hbefore
        (max old.position.bound (b old))
  simp only [Board.get] at hwrel hwlabels hwcurrent hwi hwmarker htail
  simp only [Board.get, Bool.not_false] at hwother hwsep
  rw [L.upper_min_of_zero] at hwi
  have hupOld : LabeledWord.UpToLeaf L.beta old.position.board.left :=
    ⟨(of_decide_eq_true hrOld).2.1, hlOld ▸ L.beta_lower, hbOld.le⟩
  have hcount : w.position.board.left.bodyLabels.length =
      (LabeledWord.bodyLeafCursor fine.position.board.left
        L.upper L.marker k xs).bodyLabels.length := by
    simp only [hwlabels, LabeledWord.bodyLeafCursor]
  have hysInc : ((ys.map fun y => ((∅ : Finset ℕ), y)).map Prod.snd).Pairwise (· < ·) := by
    simpa using (List.pairwise_append.mp (List.pairwise_cons.mp hfullInc).2).2.1
  obtain ⟨v, hOldV, _hvn, hvshape, hvrel, hvlabels, hvother⟩ :=
    Concrete.follow_next_leaf hHN (payoff blue) σ old false hpOld hshape hupOld hbOld
      (by simpa only [Board.get, hlOld] using hnOld) htail.run hwi hcount hwmarker hysInc (by
        intro atom ha
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        exact ⟨hKH (hys y hy).1, (le_max_left _ _).trans_lt (hys y hy).2,
          (le_max_right _ _).trans_lt (hys y hy).2⟩)
  simp only [Board.get, Bool.not_false] at hvshape hvrel hvlabels hvother
  have hvsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hOldV).reply_separation hpOld
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
  · simpa only [hstBoard, hsuBoard] using hvshape
  · simpa only [hstBoard] using hvrel
  · simpa only [hsuBoard] using hwrel
  · simpa only [hstBoard, LabeledWord.currentLabel, hvlabels] using hlOld
  · simpa only [hsuBoard] using hwcurrent
  · simpa only [hstBoard] using hvshape.leaf_eq.trans hwi
  · simpa only [hsuBoard] using hwi
  · simpa only [hstBoard] using hvlabels
  · simpa only [hsuBoard] using hwlabels
  · simpa only [hstBoard] using hvother
  · simpa only [hsuBoard] using hwother
  · simpa only [hstBoard, Board.get, Bool.not_false] using hvsep
  · simpa only [hsuBoard] using hwsep

#print axioms preliminary_zero_upper

end Erdos591.Positive.Game.Payoff
