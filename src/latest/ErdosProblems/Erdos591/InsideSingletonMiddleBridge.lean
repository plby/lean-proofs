import ErdosProblems.Erdos591.InsideTwoMiddleBridge
import ErdosProblems.Erdos591.SingletonOppositeFuture
import ErdosProblems.Erdos591.InsideDeferredMarkerEndgame

/-!
# The two middle phases when the upper opposite body label is singleton

The upper first word still has a future selected body, so the next
opposite request is a next-body advance. Keep that response pending
through the second middle phase and shared last S leaf. Only then
extend it above the lower completion bounds and apply the prefix endgame.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_singleton_middle_bridge_triangle {N H : Set ℕ}
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
    (hTcard : 2 ≤ tu.position.board.left.rootLabel.card)
    (hTfirst : ∀ i ∈ tu.position.board.left.rootLabel,
      tu.position.board.left.bodyLabels.length ≤ i)
    (hU : LabeledWord.SameStructure tu.position.board.right su.position.board.right)
    (hUrel : tu.position.board.right.relaxed = true)
    (hUcard : tu.position.board.right.currentLabel.card = 1)
    (hUstrict : su.position.board.right.leafIndex < su.position.board.right.currentLabel.sup id)
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
  obtain ⟨input, hreplyT⟩ := (History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) htuStep)).reply_of_pending hpTU
  have hTlabels := (hreplyT.advance_up_to_leaf
    ((Position.history_dataInvariant tu).2.1 false).1 hTup hTstrict).2.1
  obtain ⟨u, k, hparseT⟩ := hTup.parser_leaves ((Position.history_dataInvariant tu).2.1 false).1
  obtain ⟨Tas, hTrun, _⟩ := follow_step_word_inputs htuStep false
  have hTrootEq := hTrun.rootLabel_eq (by simp [Board.get, hparseT])
  change afterT.position.board.left.rootLabel = tu.position.board.left.rootLabel at hTrootEq
  change afterT.position.board.left.bodyLabels = tu.position.board.left.bodyLabels at hTlabels
  obtain ⟨i, hi, requestU, hUrequestPath, hUrequestBoard, hpRequestU⟩ :=
    winning_singleton_other_future_request hHN hH blue hwinAfterT false hnAfterT hrAfterT
      hsepAfterT (by simpa [hTrootEq, Board.get] using hTcard)
      (by simpa [hTrootEq, hTlabels, Board.get] using hTfirst)
      (by simpa [Board.get, hUunchanged] using hUrel)
      (by simpa [Board.get, hUunchanged] using hUcard)
  have hfuture : LabeledWord.BeforeBody i requestU.position.board.right := by
    simpa [hUrequestBoard, Board.get] using hi
  obtain ⟨nextRoot, hbeforeRoot, hleastRoot⟩ := hfuture.least_future
  have hrequestRel : requestU.position.board.right.relaxed = true := by
    simpa [hUrequestBoard, hUunchanged] using hUrel
  have hrequestNo : requestU.position.board.right.NoLeafPending :=
    LabeledWord.singleton_relaxed_no_leaf_pending hrequestRel
      (by simpa [hUrequestBoard, hUunchanged] using hUcard)
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
      hrU, hlastU, hlU, _hmU, hiU, ⟨frontS, hfrontS, hfreshS⟩,
      ⟨frontU, hfrontU, hfreshU⟩⟩ :=
    inside_second_middle hHN hH blue su hwinSU hmodeSU L hpSU hmSU hparseSU hrootSU hBSU
      full hfullLen hfullInc hfullPool C hrelU hrootU originU hMU
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
  obtain ⟨lastST, lastSU, hlastStepST, hlastStepSU, _hnLastST, _hnLastSU,
      hSlast, hrLastST, hrLastSU, hiLastST, hiLastSU, hlLastST, hlLastSU, hoLastST, hoLastSU⟩ :=
    shared_next_leaf_from_prefix hHN hH blue σ midST midSU false false hpMidST hpMidSU
      hupST (by simpa only [Board.get, hiMidST] using L.penultimate_lt_pivot) hnextST
      hupSU (by simpa only [Board.get, hiMidSU] using L.upperPenultimate_lt_pivot)
      hnextSU hanchor hfrontS
      (fun atom ha => ⟨(hfreshS atom ha).1, hCST.trans_lt (hfreshS atom ha).2⟩)
      (by simp [Board.get, hlMidSU, LabeledWord.bodyLeafCursor])
      (by simp [Board.get, hmMidSU, LabeledWord.bodyLeafCursor])
  change lastST.position.board.right = midST.position.board.right at hoLastST
  change lastSU.position.board.right = midSU.position.board.right at hoLastSU
  have hSdoneST := selected_last_leaf_exhausted hlastStepST hupST hrootMidST
    (fun i hi => L.lower_le_pivot i (hcurrentST ▸ hi)) hlLastST hiLastST
  have hSdoneSU := selected_last_leaf_exhausted hlastStepSU hupSU hrootMidSU
    (fun i hi => (L.upper_bounds i (hcurrentSU ▸ hi)).2) hlLastSU hiLastSU
  have hlastST : BothLast lastST.position.board := by
    intro side
    cases side
    · exact hSdoneST
    · simpa [Board.get, hoLastST] using hlastT
  have hlastSU : BothLast lastSU.position.board := by
    intro side
    cases side
    · exact hSdoneSU
    · simpa [Board.get, hoLastSU] using hlastU
  have hrelLastST : ∀ side, (lastST.position.board.get side).relaxed = true := by
    intro side
    cases side
    · exact hrLastST
    · simpa [Board.get, hoLastST] using hrT
  have hrelLastSU : ∀ side, (lastSU.position.board.get side).relaxed = true := by
    intro side
    cases side
    · exact hrLastSU
    · simpa [Board.get, hoLastSU] using hrU
  have hTfinal : LabeledWord.SameStructure lastST.position.board.right
      requestU.position.board.left :=
    by simpa [hoLastST, hUrequestBoard] using hTshape.symm
  have hUrequest : LabeledWord.SameStructure requestU.position.board.right
      su.position.board.right := by simpa [hUrequestBoard, hUunchanged] using hU
  exact inside_deferred_marker_endgame hHN hH blue lastST lastSU requestU
    (hwinST.of_reachable (exactGame N blue) (hstPath.tail hlastStepST))
    (hwinSU.of_reachable (exactGame N blue) (hsuPath.tail hlastStepSU))
    (hwinAfterT.of_reachable (exactGame N blue) hUrequestPath)
    (follow_mode_some (hstPath.tail hlastStepST) hmodeST)
    (follow_mode_some (hsuPath.tail hlastStepSU) hmodeSU)
    hlastST hlastSU hrelLastST hrelLastSU hSlast hTfinal hpRequestU hrequestRel hrequestNo
    hbeforeRoot hleastRoot hUrequest (by simpa [hoLastSU] using hfrontU)
    (by simpa [hoLastSU] using congrArg List.length hlU)
    (by simpa [hoLastSU, hiU] using hUstrict)
    (fun atom ha => ⟨(hfreshU atom ha).1, hCU.trans_lt (hfreshU atom ha).2⟩)

#print axioms inside_singleton_middle_bridge_triangle

end Erdos591.Positive.Game.Payoff
