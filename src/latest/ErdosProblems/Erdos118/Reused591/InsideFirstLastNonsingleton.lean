import ErdosProblems.Erdos118.Reused591.FirstLastInterior
import ErdosProblems.Erdos118.Reused591.KnownMiddleReplay
import ErdosProblems.Erdos118.Reused591.DeferredNextLeaf
import ErdosProblems.Erdos118.Reused591.InsideSharedLeafEndgame

namespace Erdos118.Reused591

/-!
# The nonsingleton ending after three paired last-body first leaves

The first-word labels have a common first and last selection, with
separated interiors. Replay the first opposite last leaf, resume the
second lower middle above both newly recorded bounds, replay its
opposite last leaf, and apply the checked shared-final-leaf endgame.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_first_last_nonsingleton_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su tu : Concrete.Hist N) {B p q : ℕ} (S : FirstLastLabels H B p q)
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hmodeST : st.position.mode = some true) (hmodeSU : su.position.mode = some true)
    (hpSU : su.position.pending = some ⟨false, .advance 0⟩)
    (hpTU : tu.position.pending = some ⟨false, .advance 0⟩)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hrST : st.position.board.left.relaxed = true) (hrSU : su.position.board.left.relaxed = true)
    (hlabelST : st.position.board.left.currentLabel = S.lower)
    (hlabelSU : su.position.board.left.currentLabel = S.upper)
    (hindexST : st.position.board.left.leafIndex = S.first)
    (hindexSU : su.position.board.left.leafIndex = S.first)
    (hrootST : ∀ i ∈ st.position.board.left.rootLabel, i ≤ st.position.board.left.bodyLabels.length)
    (hrootSU : ∀ i ∈ su.position.board.left.rootLabel, i ≤ su.position.board.left.bodyLabels.length)
    (hrT : st.position.board.right.relaxed = true) (hrU : su.position.board.right.relaxed = true)
    (hrootT : ∀ i ∈ st.position.board.right.rootLabel,
      i ≤ st.position.board.right.bodyLabels.length)
    (hrootU : ∀ i ∈ su.position.board.right.rootLabel,
      i ≤ su.position.board.right.bodyLabels.length)
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
      tu.position.board.right.leafIndex < i → su.position.board.right.currentLabel.sup id ≤ i) :
    ¬ blue.CliqueFree 3 := by
  let D := max (max su.position.bound (b su)) (max tu.position.bound (b tu))
  have hDSU : max su.position.bound (b su) ≤ D := le_max_left _ _
  have hDTU : max tu.position.bound (b tu) ≤ D := le_max_right _ _
  have hSTstrict : st.position.board.left.leafIndex < S.lowerPenultimate := by
    rw [hindexST]
    exact S.first_lt_lowerPenultimate hp
  have hSTup : LabeledWord.UpToLeaf S.lowerPenultimate st.position.board.left :=
    ⟨(of_decide_eq_true hrST).2.1, hlabelST ▸ S.lowerPenultimate_mem, hSTstrict.le⟩
  obtain ⟨midST, afterT, hSTpath, hTUstep, hpMidST, _hnAfterT, hrMidST, hiMidST,
      hlMidST, hmMidST, hrMidT, hlastT, _hlMidT, _hmMidT, _hiMidT,
      hTshape, hrAfterT, hUunchanged, hinputsST⟩ :=
    known_middle_opposite_replay hHN hH blue st tu hwinST hmodeST hSTup
      S.lowerPenultimate_lt_last (hlabelST ▸ S.last_lower)
      (by simpa only [hlabelST] using S.lower_bounds_penultimate) hrootST hrT hrootT
      (Or.inl hSTstrict) false hpTU hT hTup hTstrict hTnext D hDTU
  change afterT.position.board.right = tu.position.board.right at hUunchanged
  have hwinAfterT := hwinTU.of_reachable (exactGame N blue) (.single hTUstep)
  have hsepAfterT :=
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hTUstep).reply_separation hpTU
  obtain ⟨requestU, hUrequestPath, hUrequestBoard, hpRequestU⟩ :=
    winning_next_leaf_request_after_other hHN hH blue hwinAfterT true
      (by simpa only [Board.get, hUunchanged] using hUup)
      (by simpa only [Board.get, hUunchanged] using hUstrict) hrAfterT hsepAfterT
  let C := max (max midST.position.bound (b midST))
    (max requestU.position.bound (b requestU))
  have hCST : max midST.position.bound (b midST) ≤ C := le_max_left _ _
  have hCU : max requestU.position.bound (b requestU) ≤ C := le_max_right _ _
  obtain ⟨frontST, hfrontST, hpoolST⟩ := hinputsST false
  change LabeledWord.LegalRun st.position.board.left frontST midST.position.board.left at hfrontST
  have hSUnextUp : LabeledWord.UpToLeaf S.upperNext su.position.board.left :=
    ⟨(of_decide_eq_true hrSU).2.1, hlabelSU ▸ S.upperNext_mem,
      by rw [hindexSU]; exact S.first_lt_upperNext.le⟩
  have hSUnext : ∀ i ∈ su.position.board.left.currentLabel,
      su.position.board.left.leafIndex < i → S.upperNext ≤ i := by
    simpa only [hlabelSU, hindexSU] using S.upperNext_le
  obtain ⟨firstSU, hSUstep, hnFirstSU, hrFirstSU, hiFirstSU, hlFirstSU, hmFirstSU,
      hUfirstSame, hsepFirstSU, anchor, hanchor, firstAtoms, hfirstRun, hfirstPool⟩ :=
    deferred_next_leaf_from_prefix hHN hH blue σ su false hpSU hSUnextUp
      (by change su.position.board.left.leafIndex < S.upperNext
          rw [hindexSU]; exact S.first_lt_upperNext) hSUnext hS.symm hfrontST
      (congrArg List.length hlMidST) hmMidST
      (by rw [hiMidST]; exact S.lowerPenultimate_lt_upperNext)
      ((Position.history_dataInvariant midST).2.1 false).2
      (fun atom hatom => ⟨(hpoolST atom hatom).1, hDSU.trans_lt (hpoolST atom hatom).2⟩) C
  change firstSU.position.board.left.relaxed = true at hrFirstSU
  change firstSU.position.board.left.leafIndex = S.upperNext at hiFirstSU
  change firstSU.position.board.left.bodyLabels = su.position.board.left.bodyLabels at hlFirstSU
  change firstSU.position.board.left.bodyMarker = su.position.board.left.bodyMarker at hmFirstSU
  change firstSU.position.board.right = su.position.board.right at hUfirstSame
  have hcurrentFirstSU : firstSU.position.board.left.currentLabel = S.upper := by
    simpa only [LabeledWord.currentLabel, hlFirstSU] using hlabelSU
  have hfirstTarget : LabeledWord.UpToLeaf S.upperPenultimate firstSU.position.board.left :=
    ⟨(of_decide_eq_true hrFirstSU).2.1, hcurrentFirstSU ▸ S.upperPenultimate_mem,
      by rw [hiFirstSU]; exact S.upperNext_le_upperPenultimate hq⟩
  have hstartSU := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant su).2.1 false).1 hrSU
  obtain ⟨as, has, _⟩ := follow_step_word_inputs hSUstep false
  have hfirstRoot : firstSU.position.board.left.rootLabel = su.position.board.left.rootLabel :=
    has.rootLabel_eq hstartSU
  have hrootFirstSU : ∀ i ∈ firstSU.position.board.left.rootLabel,
      i ≤ firstSU.position.board.left.bodyLabels.length := by
    simpa only [hfirstRoot, hlFirstSU] using hrootSU
  have hreqUShape : LabeledWord.SameStructure requestU.position.board.right
      firstSU.position.board.right := by
    simpa only [hUrequestBoard, hUunchanged, hUfirstSame] using hU
  obtain ⟨midSU, lastTU, hSUpath, hUstep, hpMidSU, _hnLastTU, hrMidSU, hiMidSU,
      hlMidSU, hmMidSU, hrMidU, hlastU, _hlMidU, _hmMidU, _hiMidU,
      hUshape, _hrLastU, hTunchanged, hinputsSU⟩ :=
    known_middle_opposite_replay hHN hH blue firstSU requestU
      (hwinSU.of_reachable (exactGame N blue) (.single hSUstep))
      (follow_mode_some (.single hSUstep) hmodeSU) hfirstTarget S.upperPenultimate_lt_last
      (hcurrentFirstSU ▸ S.last_upper)
      (by simpa only [hcurrentFirstSU] using S.upper_bounds_penultimate) hrootFirstSU
      (by simpa only [hUfirstSame] using hrU) (by simpa only [hUfirstSame] using hrootU)
      (Or.inr ⟨hnFirstSU, hsepFirstSU⟩) true hpRequestU hreqUShape
      (by simpa only [Board.get, hUrequestBoard, hUunchanged, hUfirstSame] using hUup)
      (by simpa only [Board.get, hUrequestBoard, hUunchanged, hUfirstSame] using hUstrict)
      (by simpa only [Board.get, hUrequestBoard, hUunchanged, hUfirstSame] using hUnext) C hCU
  have hTlast : LabeledWord.SameStructure midST.position.board.right lastTU.position.board.left :=
    by simpa only [show lastTU.position.board.left = requestU.position.board.left from hTunchanged,
      hUrequestBoard, Board.get] using hTshape.symm
  have hUlast : LabeledWord.SameStructure midSU.position.board.right lastTU.position.board.right :=
    hUshape.symm
  obtain ⟨secondAtoms, hsecondRun, hsecondPool⟩ := hinputsSU false
  change LabeledWord.LegalRun firstSU.position.board.left secondAtoms midSU.position.board.left
    at hsecondRun
  have hfullS := hfirstRun.append hsecondRun
  have hfullPool : ∀ atom ∈ firstAtoms ++ secondAtoms,
      atom.2 ∈ H ∧ max midST.position.bound (b midST) < atom.2 := by
    intro atom hatom
    have hf : atom.2 ∈ H ∧ C < atom.2 :=
      (List.mem_append.mp hatom).elim (hfirstPool atom) (hsecondPool atom)
    exact ⟨hf.1, hCST.trans_lt hf.2⟩
  have hlabelMidST : midST.position.board.left.currentLabel = S.lower := by
    simpa only [LabeledWord.currentLabel, hlMidST] using hlabelST
  have hlabelMidSU : midSU.position.board.left.currentLabel = S.upper := by
    simpa only [LabeledWord.currentLabel, hlMidSU, hlFirstSU] using hlabelSU
  have hlastUpST : LabeledWord.UpToLeaf S.last midST.position.board.left :=
    ⟨(of_decide_eq_true hrMidST).2.1, hlabelMidST ▸ S.last_lower,
      by rw [hiMidST]; exact S.lowerPenultimate_lt_last.le⟩
  have hlastUpSU : LabeledWord.UpToLeaf S.last midSU.position.board.left :=
    ⟨(of_decide_eq_true hrMidSU).2.1, hlabelMidSU ▸ S.last_upper,
      by rw [hiMidSU]; exact S.upperPenultimate_lt_last.le⟩
  have hlastNextST : ∀ i ∈ midST.position.board.left.currentLabel,
      midST.position.board.left.leafIndex < i → S.last ≤ i := by
    intro i hi hlt
    rcases S.lower_bounds_penultimate i (hlabelMidST ▸ hi) with heq | hle
    · exact heq.ge
    · rw [hiMidST] at hlt
      exact (not_lt_of_ge hle hlt).elim
  have hlastNextSU : ∀ i ∈ midSU.position.board.left.currentLabel,
      midSU.position.board.left.leafIndex < i → S.last ≤ i := by
    intro i hi hlt
    rcases S.upper_bounds_penultimate i (hlabelMidSU ▸ hi) with heq | hle
    · exact heq.ge
    · rw [hiMidSU] at hlt
      exact (not_lt_of_ge hle hlt).elim
  obtain ⟨bs, hbs, _⟩ := follow_word_inputs hSTpath 0 (fun _ => Nat.zero_le _) false
  change LabeledWord.LegalRun st.position.board.left bs midST.position.board.left at hbs
  have hrootMidST : ∀ i ∈ midST.position.board.left.rootLabel,
      i ≤ midST.position.board.left.bodyLabels.length := by
    simpa only [hbs.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant st).2.1 false).1 hrST), hlMidST] using hrootST
  have hrootMidSU : ∀ i ∈ midSU.position.board.left.rootLabel,
      i ≤ midSU.position.board.left.bodyLabels.length := by
    simpa only [hsecondRun.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant firstSU).2.1 false).1 hrFirstSU), hlMidSU] using hrootFirstSU
  have hcount : midSU.position.board.left.bodyLabels.length = anchor.bodyLabels.length :=
    (congrArg List.length (hlMidSU.trans hlFirstSU)).trans
      (hS.body_length.symm.trans ((congrArg List.length hlMidST).symm.trans hanchor.body_length))
  have hmarker : midSU.position.board.left.bodyMarker = anchor.bodyMarker :=
    (hmMidSU.trans hmFirstSU).trans
      (hS.bodyMarker_eq.symm.trans (hmMidST.symm.trans hanchor.bodyMarker_eq))
  exact inside_shared_leaf_triangle hHN hH blue midST midSU lastTU
    (hwinST.of_reachable (exactGame N blue) hSTpath)
    (hwinSU.of_reachable (exactGame N blue) (hSUpath.head hSUstep))
    (hwinAfterT.of_reachable (exactGame N blue) (hUrequestPath.tail hUstep))
    (follow_mode_some hSTpath hmodeST)
    (follow_mode_some (hSUpath.head hSUstep) hmodeSU) hpMidST hpMidSU hlastUpST
    (by rw [hiMidST]; exact S.lowerPenultimate_lt_last) hlastNextST hlastUpSU
    (by rw [hiMidSU]; exact S.upperPenultimate_lt_last) hlastNextSU hrootMidST hrootMidSU
    (fun i hi => (S.lower_bounds i (hlabelMidST ▸ hi)).2)
    (fun i hi => (S.upper_bounds i (hlabelMidSU ▸ hi)).2)
    hanchor hfullS hfullPool hcount hmarker hrMidT hrMidU hlastT hlastU hTlast hUlast

#print axioms inside_first_last_nonsingleton_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
