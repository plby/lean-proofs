import ErdosProblems.Erdos118.Reused591.PlainLastLeafCheckpoint
import ErdosProblems.Erdos118.Reused591.ReachSelectedLeaf

namespace Erdos118.Reused591

/-!
# Stop the lower finishing play before its final S leaf

The opposite word is initially freshest. If the penultimate S leaf is
already current, issue the last S request immediately. Otherwise reach
that leaf, take the ordinary opposite selected leaf, and issue the last
S request. The opposite selected part is exhausted in both cases.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem last_body_final_request {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0)
    (hroot : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    {gamma : ℕ} (hgamma : gamma ∈ p.position.board.left.currentLabel)
    (hbefore : p.position.board.left.leafIndex < gamma)
    (hlast : ∀ x ∈ p.position.board.left.currentLabel, x ≤ gamma) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left.relaxed = true ∧ q.position.board.right.relaxed = true ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ∧
      q.position.board.left.rootLabel = p.position.board.left.rootLabel ∧
      q.position.board.left.leafIndex < gamma ∧
      (∀ x ∈ q.position.board.left.currentLabel,
        q.position.board.left.leafIndex < x → gamma ≤ x) ∧
      (∀ x ∈ q.position.board.left.coordinates,
        x ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ¬ Macro.Pending q.position.board.right := by
  classical
  let C := p.position.board.left.currentLabel
  let D := C.erase gamma
  have hmem : p.position.board.left.leafIndex ∈ D :=
    Finset.mem_erase.mpr ⟨hbefore.ne, (of_decide_eq_true hl).2.2⟩
  let pen := D.sup id
  have hpenD : pen ∈ D := by
    simpa [pen] using Finset.sup_mem_of_nonempty (f := id) ⟨_, hmem⟩
  have hpenC : pen ∈ C := Finset.mem_of_mem_erase hpenD
  have hpenLt : pen < gamma := lt_of_le_of_ne (hlast pen hpenC) (Finset.ne_of_mem_erase hpenD)
  have hle : p.position.board.left.leafIndex ≤ pen := Finset.le_sup (f := id) hmem
  have hnext : ∀ x ∈ C, pen < x → gamma ≤ x := by
    intro x hx hlt
    by_contra hn
    have hmemD : x ∈ D := Finset.mem_erase.mpr ⟨(lt_of_not_ge hn).ne, hx⟩
    exact not_lt_of_ge (Finset.le_sup (f := id) hmemD) hlt
  have hstart := LabeledWord.relaxed_ne_start ((Position.history_dataInvariant p).2.1 false).1 hl
  rcases lt_or_eq_of_le hle with hstrict | heq
  · obtain ⟨v, hpv, _hvn, hvl, hvi, hvb, _hvm, hvsep⟩ :=
      winning_reach_selected_leaf_fresh hHN hH blue hwin false pen
        ⟨(of_decide_eq_true hl).2.1, hpenC, hle⟩ hstrict
    change v.position.board.left.bodyLabels = p.position.board.left.bodyLabels at hvb
    change v.position.board.left.leafIndex = pen at hvi
    obtain ⟨as, has, _⟩ := follow_word_inputs hpv 0 (fun _ => Nat.zero_le _) false
    have hvroot : v.position.board.left.rootLabel = p.position.board.left.rootLabel :=
      has.rootLabel_eq hstart
    have hvcurrent : v.position.board.left.currentLabel = C := by
      simp only [C, LabeledWord.currentLabel, hvb]
    have hVroot : ∀ i ∈ v.position.board.left.rootLabel,
        i ≤ v.position.board.left.bodyLabels.length := by
      simpa only [hvroot, hvb] using hroot
    obtain ⟨q, hvq, hpq, hqleft, hqr, hqsep, hno⟩ := plain_last_leaf_checkpoint hHN hH blue
      (hwin.of_reachable (exactGame N blue) hpv) (follow_mode_some hpv hmode) hvl hvsep
      ⟨(of_decide_eq_true hvl).2.1, by rw [hvcurrent]; exact hgamma,
        by simpa only [hvi] using hpenLt.le⟩
      (by simpa only [hvi] using hpenLt) (by simpa only [hvcurrent, hvi] using hnext)
      hVroot (by simpa only [hvcurrent] using hlast)
    refine ⟨q, hpv.trans hvq, hpq, ?_, hqr, ?_, ?_, ?_, ?_, hqsep, hno⟩
    · simpa only [hqleft, Board.get] using hvl
    · simpa only [hqleft] using hvb
    · simpa only [hqleft] using hvroot
    · simpa only [hqleft, hvi] using hpenLt
    · simpa only [hqleft, hvcurrent, hvi] using hnext
  · obtain ⟨q, hpq, hboard, hp⟩ := winning_next_leaf_request_after_other hHN hH blue hwin false
      ⟨(of_decide_eq_true hl).2.1, hgamma, hbefore.le⟩ hbefore hr hsep
    have hno := winning_before_last_leaf_other_exhausted hHN hH blue
      (hwin.of_reachable (exactGame N blue) hpq) (follow_mode_some hpq hmode) hp
      (by simpa only [hboard] using
        (show LabeledWord.UpToLeaf gamma p.position.board.left from
          ⟨(of_decide_eq_true hl).2.1, hgamma, hbefore.le⟩))
      (by simpa only [hboard] using hbefore)
      (by simpa only [hboard, heq] using hnext)
      (by simpa only [hboard] using hroot) (by simpa only [hboard] using hlast)
      (by simpa only [hboard, Board.get] using (LabeledWord.relaxed_ne_start
        ((Position.history_dataInvariant p).2.1 true).1 hr))
    refine ⟨q, hpq, hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hno⟩
    · simpa only [hboard] using hl
    · simpa only [hboard] using hr
    · simp only [hboard]
    · simp only [hboard]
    · simpa only [hboard] using hbefore
    · simpa only [hboard, heq] using hnext
    · simpa only [hboard] using hsep

#print axioms last_body_final_request

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
