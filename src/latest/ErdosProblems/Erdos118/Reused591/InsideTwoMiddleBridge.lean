import ErdosProblems.Erdos118.Reused591.InsideFirstMiddle
import ErdosProblems.Erdos118.Reused591.InsideSecondMiddle
import ErdosProblems.Erdos118.Reused591.InsideSharedLeafEndgame
import ErdosProblems.Erdos118.Reused591.PendingNextLeaf

namespace Erdos118.Reused591

/-!
# The two middle phases when both upper opposite next leaves are reserved

Start at the paired last-body requests and the upper next-T request.
Choose the common-last body labels only now. The first middle phase
fixes the next-U bound; the second phase respects both new bounds.
Replay U, share the last S leaf, and apply the checked inside endgame.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_two_middle_bridge_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su tu : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hmodeST : st.position.mode = some true) (hmodeSU : su.position.mode = some true)
    {a c : ℕ} (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hpST : st.position.pending = some ⟨false, .advance a⟩)
    (hpSU : su.position.pending = some ⟨false, .advance c⟩)
    (hmST : st.position.board.left.markerEvent = true)
    (hmSU : su.position.board.left.markerEvent = true)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hrootST : ∀ i ∈ st.position.board.left.rootLabel,
      i ≤ st.position.board.left.bodyLabels.length + 1)
    (hrootSU : ∀ i ∈ su.position.board.left.rootLabel,
      i ≤ su.position.board.left.bodyLabels.length + 1)
    (hrelT : st.position.board.right.relaxed = true)
    (hrelU : su.position.board.right.relaxed = true)
    (hrootT : ∀ i ∈ st.position.board.right.rootLabel,
      i ≤ st.position.board.right.bodyLabels.length)
    (hrootU : ∀ i ∈ su.position.board.right.rootLabel,
      i ≤ su.position.board.right.bodyLabels.length)
    (hpTU : tu.position.pending = some ⟨false, .advance 0⟩)
    (hT : LabeledWord.SameStructure tu.position.board.left st.position.board.right)
    (hTup : LabeledWord.UpToLeaf (st.position.board.right.currentLabel.sup id)
      tu.position.board.left)
    (hTstrict : tu.position.board.left.leafIndex < st.position.board.right.currentLabel.sup id)
    (hTnext : ∀ i ∈ tu.position.board.left.currentLabel,
      tu.position.board.left.leafIndex < i → st.position.board.right.currentLabel.sup id ≤ i)
    (hU : LabeledWord.SameStructure tu.position.board.right su.position.board.right)
    (hUup : LabeledWord.UpToLeaf (su.position.board.right.currentLabel.sup id)
      tu.position.board.right)
    (hUstrict : tu.position.board.right.leafIndex < su.position.board.right.currentLabel.sup id)
    (hUnext : ∀ i ∈ tu.position.board.right.currentLabel,
      tu.position.board.right.leafIndex < i → su.position.board.right.currentLabel.sup id ≤ i)
    {targetT targetU modeT modeU : Bool} {otherT otherU : LabeledWord}
    (originT originU : Concrete.Hist N)
    (hMT : ∃ M : Managed N H blue b σ targetT modeT otherT st.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) originT M.target)
    (hMU : ∃ M : Managed N H blue b σ targetU modeU otherU su.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) originU M.target) :
    ¬ blue.CliqueFree 3 := by
  let B := max (max st.position.bound (b st))
    (max (max su.position.bound (b su)) (max tu.position.bound (b tu)))
  have hBST : max st.position.bound (b st) ≤ B := le_max_left _ _
  have hBSU : max su.position.bound (b su) ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBTU : max tu.position.bound (b tu) ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨L⟩ := LastLastLabels.exists_sizes_of_infinite hH B a c ha hc
  obtain ⟨midST, afterT, hstPath, htuStep, hpMidST, hnAfterT, hrMidST, hiMidST,
      hlMidST, hmMidST, hrT, hlastT, _hlT, _hmT, _hiT, hTshape, hrAfterT, hUunchanged,
      first, r, xs, _hfirstStep, hmiddlePath, hparse, hfirstWord, _hfirstOther,
      _hfirstBound, _hxsLen, _hxsInc, hxsPool, _hinputs⟩ :=
    inside_first_middle hHN hH blue st tu hwinST hmodeST L hpST hmST hrootST hBST
      hrelT hrootT hpTU hT hTup hTstrict hTnext hBTU originT hMT
  have hwinAfterT := hwinTU.of_reachable (exactGame N blue) (.single htuStep)
  have hsepAfterT :=
    (FiniteResponseGame.FollowStep.next (exactGame N blue) htuStep).reply_separation hpTU
  obtain ⟨requestU, hUrequestPath, hUrequestBoard, hpRequestU⟩ :=
    winning_next_leaf_request_after_other hHN hH blue hwinAfterT true
      (by simpa [Board.get, hUunchanged] using hUup)
      (by simpa [Board.get, hUunchanged] using hUstrict) hrAfterT hsepAfterT
  obtain ⟨full, hfullLen, hfullInc, hfullPool, hfullShape⟩ :=
    first_middle_prefix st first midST L xs hparse hfirstWord hmiddlePath hlMidST hiMidST
      (fun x hx => (hxsPool x hx).1)
  have hparseSU : su.position.board.left.parser = .blocks (r + 1) :=
    hS.parser_eq.symm.trans hparse
  let C := max (max midST.position.bound (b midST))
    (max requestU.position.bound (b requestU))
  have hCST : max midST.position.bound (b midST) ≤ C := le_max_left _ _
  have hCU : max requestU.position.bound (b requestU) ≤ C := le_max_right _ _
  obtain ⟨midSU, hsuPath, hpMidSU, hrMidSU, hiMidSU, hlMidSU, hmMidSU, hrootMidSU,
      hrU, hlastU, hlU, hmU, hiU, ⟨frontS, hfrontS, hfreshS⟩,
      ⟨frontU, hfrontU, hfreshU⟩⟩ :=
    inside_second_middle hHN hH blue su hwinSU hmodeSU L hpSU hmSU hparseSU hrootSU hBSU
      full hfullLen hfullInc hfullPool C hrelU hrootU originU hMU
  have hUrequest : LabeledWord.SameStructure requestU.position.board.right
      su.position.board.right := by simpa [hUrequestBoard, hUunchanged] using hU
  have hUinc : (frontU.map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant midSU).2.1 true).2
    change midSU.position.board.right.coordinates.Pairwise (· < ·) at hi
    rw [LabeledWord.runAtoms_coordinates hfrontU.run] at hi
    exact (List.pairwise_append.mp hi).2.1
  obtain ⟨lastTU, hUstep, _hnLastTU, hUshape, _hrLastU, _hlLastU, hTunchanged⟩ :=
    Concrete.follow_next_leaf hHN (payoff blue) σ requestU true hpRequestU hUrequest
      (by simpa [Board.get, hUrequestBoard, hUunchanged] using hUup)
      (by simpa [Board.get, hUrequestBoard, hUunchanged] using hUstrict)
      (by simpa [Board.get, hUrequestBoard, hUunchanged] using hUnext)
      hfrontU.run hiU (congrArg List.length hlU) hmU hUinc (fun atom ha =>
        ⟨(hfreshU atom ha).1, ((le_max_left _ _).trans hCU).trans_lt (hfreshU atom ha).2,
          ((le_max_right _ _).trans hCU).trans_lt (hfreshU atom ha).2⟩)
  have hTlast : LabeledWord.SameStructure midST.position.board.right lastTU.position.board.left :=
    by simpa [show lastTU.position.board.left = requestU.position.board.left from hTunchanged,
      hUrequestBoard] using hTshape.symm
  have hUlast : LabeledWord.SameStructure midSU.position.board.right lastTU.position.board.right :=
    hUshape.symm
  have hanchor : LabeledWord.SameStructure midST.position.board.left
      (LabeledWord.bodyLeafCursor su.position.board.left L.upper L.marker r full) :=
    hfullShape.trans (hS.bodyLeafCursor L.lower L.upper L.marker r full)
  have hcurrentST : midST.position.board.left.currentLabel = L.lower := by
    simp [LabeledWord.currentLabel, hlMidST]
  have hcurrentSU : midSU.position.board.left.currentLabel = L.upper := by
    simp [LabeledWord.currentLabel, hlMidSU]
  have hupST : LabeledWord.UpToLeaf L.pivot midST.position.board.left :=
    ⟨(of_decide_eq_true hrMidST).2.1, hcurrentST ▸ L.pivot_lower,
      by rw [hiMidST]; exact L.penultimate_lt_pivot.le⟩
  have hupSU : LabeledWord.UpToLeaf L.pivot midSU.position.board.left :=
    ⟨(of_decide_eq_true hrMidSU).2.1, hcurrentSU ▸ L.pivot_upper,
      by rw [hiMidSU]; exact L.upperPenultimate_lt_pivot.le⟩
  have hnextST : ∀ i ∈ midST.position.board.left.currentLabel,
      midST.position.board.left.leafIndex < i → L.pivot ≤ i := by
    intro i hi hlt
    rcases L.lower_bounds i (hcurrentST ▸ hi) with heq | hle
    · exact heq.ge
    · rw [hiMidST] at hlt
      exact (not_lt_of_ge hle hlt).elim
  have hnextSU : ∀ i ∈ midSU.position.board.left.currentLabel,
      midSU.position.board.left.leafIndex < i → L.pivot ≤ i := by
    intro i hi hlt
    rcases L.upper_bounds_penultimate i (hcurrentSU ▸ hi) with heq | hle
    · exact heq.ge
    · rw [hiMidSU] at hlt
      exact (not_lt_of_ge hle hlt).elim
  obtain ⟨Sas, hSrun, _⟩ := follow_word_inputs hstPath 0 (fun _ => Nat.zero_le _) false
  have hSTrootEq := hSrun.rootLabel_eq (by simp [Board.get, hparse])
  have hrootMidST : ∀ i ∈ midST.position.board.left.rootLabel,
      i ≤ midST.position.board.left.bodyLabels.length := by
    intro i hi
    simpa [hlMidST] using hrootST i (hSTrootEq ▸ hi)
  exact inside_shared_leaf_triangle hHN hH blue midST midSU lastTU
    (hwinST.of_reachable (exactGame N blue) hstPath)
    (hwinSU.of_reachable (exactGame N blue) hsuPath)
    (hwinAfterT.of_reachable (exactGame N blue) (hUrequestPath.tail hUstep))
    (follow_mode_some hstPath hmodeST) (follow_mode_some hsuPath hmodeSU)
    hpMidST hpMidSU hupST (by rw [hiMidST]; exact L.penultimate_lt_pivot) hnextST
    hupSU (by rw [hiMidSU]; exact L.upperPenultimate_lt_pivot) hnextSU
    hrootMidST hrootMidSU
    (fun i hi => L.lower_le_pivot i (hcurrentST ▸ hi))
    (fun i hi => (L.upper_bounds i (hcurrentSU ▸ hi)).2)
    hanchor hfrontS (fun atom ha => ⟨(hfreshS atom ha).1, hCST.trans_lt (hfreshS atom ha).2⟩)
    (by simp [hlMidSU, LabeledWord.bodyLeafCursor])
    (by simp [hmMidSU, LabeledWord.bodyLeafCursor]) hrT hrU hlastT hlastU hTlast hUlast

#print axioms inside_two_middle_bridge_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
