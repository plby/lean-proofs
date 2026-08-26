import ErdosProblems.Erdos591.SplicedAnchorMarker
import ErdosProblems.Erdos591.FirstLeafGluingHistory

/-! # The shared anchor from a selected marker at or before it -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_spliced_anchor_from_marker {N H HU : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} {B e g j k : ℕ} (U : SplicedRootLabels HU B e g j k)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hn : p.position.pending = none)
    (hl : p.position.board.left.relaxed = true)
    (hm : p.position.board.right.markerEvent = true)
    (hbeforeT : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hindex : p.position.board.right.bodyLabels.length + 1 ≤ U.anchor)
    (hUroot : p.position.board.right.rootLabel = U.upper)
    (hmode : p.position.mode = some true)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨true, .advance d⟩ ∧ 0 < d ∧
      q.position.board.right.markerEvent = true ∧
      q.position.board.right.bodyLabels.length + 1 = U.anchor ∧
      q.position.board.right.rootLabel = U.upper ∧
      q.position.board.left.rootLabel = p.position.board.left.rootLabel ∧
      q.position.board.left.bodyLabels.length < q.position.board.left.lastSelectedBody := by
  obtain ⟨v, d, hpv, hboard, hp, hd⟩ := winning_request_at_marker hHN hH blue hwin true hn hm
  by_cases heq : p.position.board.right.bodyLabels.length + 1 = U.anchor
  · exact ⟨v, d, .single hpv, hp, hd, by simpa only [hboard] using hm,
      by simpa only [hboard] using heq, by simpa only [hboard] using hUroot,
      by simp only [hboard], by simpa only [hboard] using hbeforeT⟩
  let C := max v.position.bound (b v)
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH C 1 d (by omega) hd
  obtain ⟨first, _other, hvf, _ho, hfn, _hon, _hs, hfr, _hor, _hi, _hoi,
      hfb, _hob, hfo, _hoo⟩ := first_leaf_gluing hHN hH blue σ v v true true
        L L rfl rfl hp hp (by simpa only [hboard, Board.get] using hm)
        (by simpa only [hboard, Board.get] using hm)
        (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  simp only [Board.get, Bool.not_true] at hfr hfb hfo
  have hpf := (Relation.ReflTransGen.single hpv).tail hvf
  have hleft : first.position.board.left = p.position.board.left := by
    simpa only [hboard] using hfo
  have hfbody : first.position.board.right.bodyLabels.length =
      p.position.board.right.bodyLabels.length + 1 := by
    simp only [hfb, List.length_append, List.length_singleton, hboard]
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
  have hstart : p.position.board.right.parser ≠ .start := by
    simp only [hparse, ne_eq, reduceCtorEq, not_false_eq_true]
  obtain ⟨as, has, _⟩ :=
    (History.reachable_word_extension (follow_history_path hpf)).2 true
  have hfroot : first.position.board.right.rootLabel = U.upper :=
    (has.rootLabel_eq hstart).trans hUroot
  have hfsep : ∀ x ∈ first.position.board.left.coordinates,
      x ≤ first.position.board.right.coordinates.getLastD 0 := by
    simpa only [Board.get, Bool.not_true] using
      (FiniteResponseGame.FollowStep.next (exactGame N blue) hvf).reply_separation hp
  obtain ⟨q, c, hfq, hpq, hc, hqm, hqi, hqr, hql, hqb⟩ :=
    winning_spliced_anchor_marker hHN hH blue U
      (hwin.of_reachable (exactGame N blue) hpf) hfn
      (by simpa only [hleft] using hl) hfr
      (by simpa only [hleft] using hbeforeT) (by rw [hfbody]; omega) hfroot hfsep
      (follow_mode_some hpf hmode)
      (fun z w hfz hz => hfixed z w (hpf.trans hfz) hz)
      (fun z w hfz hz => hlast z w (hpf.trans hfz) hz)
  exact ⟨q, c, hpf.trans hfq, hpq, hc, hqm, hqi, hqr,
    by simpa only [hleft] using hql, hqb⟩

#print axioms winning_spliced_anchor_from_marker

end Erdos591.Positive.Game.Payoff
