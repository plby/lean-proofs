import ErdosProblems.Erdos591.ReachPenultimateOrCurrent
import ErdosProblems.Erdos591.CriticalOpeningHandoff
import ErdosProblems.Erdos591.OvertakenOtherRelaxed

/-!
# Reach the upper critical checkpoint without moving a paused lower play

The only play extended here is the supplied winning play. It either
already has the first word's penultimate endpoint followed by an opposite
selected leaf, or reaches that endpoint and takes one opposite leaf.
The bounded form records literal fresh input runs for later coarse replay.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_reach_critical_checkpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hn : p.position.pending = none)
    (hl : p.position.board.left.relaxed = true)
    (hr : p.position.board.right.relaxed = true)
    (hbefore : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ CriticalCheckpoint q := by
  obtain ⟨v, hpv, hvn, hvl, hvno, _hvroot, hvbefore, hvpen, hcurrent⟩ :=
    winning_reach_penultimate_body_or_current hHN hH blue hwin false hn hl hbefore
  simp only [Board.get, Bool.not_false] at hvl hvno hvbefore hvpen hcurrent
  rcases hcurrent with heq | hvsep
  · subst v
    obtain ⟨as, has⟩ := History.word_run p false
    obtain ⟨_hl, horder⟩ := winning_overtaken_other_relaxed hHN hH blue hwin true hr
      (has.relaxed_coordinates_pos hl) hsep
    exact ⟨p, .refl, hn, hl, hr, horder, hbefore, hvpen, hvno⟩
  · have hmem : v.position.board.left.lastSelectedBody ∈ v.position.board.left.rootLabel := by
      simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
        ⟨_, (of_decide_eq_true hvl).2.1⟩
    obtain ⟨q, hvq, hqn, hqr, hqo, hqsep⟩ :=
      winning_next_opposite_leaf hHN hH blue
        (hwin.of_reachable (exactGame N blue) hpv) false hvl hvsep
        (Or.inl ⟨_, hmem, hvbefore⟩)
    simp only [Board.get, Bool.not_false] at hqr hqo hqsep
    have hleft : q.position.board.left = v.position.board.left := hqo
    have hql : q.position.board.left.relaxed = true := by simpa only [hleft] using hvl
    obtain ⟨as, has⟩ := History.word_run q false
    obtain ⟨_hl, horder⟩ := winning_overtaken_other_relaxed hHN hH blue
      (hwin.of_reachable (exactGame N blue) (hpv.trans hvq)) true hqr
        (has.relaxed_coordinates_pos hql) hqsep
    refine ⟨q, hpv.trans hvq, hqn, hql, hqr, horder, ?_, ?_, ?_⟩
    · simpa only [hleft] using hvbefore
    · simpa only [hleft] using hvpen
    · simpa only [hleft] using hvno

theorem winning_reach_critical_checkpoint_above {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hn : p.position.pending = none)
    (hl : p.position.board.left.relaxed = true)
    (hr : p.position.board.right.relaxed = true)
    (hbefore : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0) (B : ℕ) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ CriticalCheckpoint q ∧
      ∀ side, ∃ as,
        LabeledWord.LegalRun (p.position.board.get side) as (q.position.board.get side) ∧
        ∀ a ∈ as, a.2 ∈ H ∧ B < a.2 := by
  let c : Concrete.Hist N → ℕ := fun v => max (b v) B
  have hwinC := hwin.mono (exactGame N blue) (Set.Subset.refl H)
    (fun v => le_max_left (b v) B)
  obtain ⟨q, hpq, hqn, hq⟩ := winning_reach_critical_checkpoint hHN hH blue hwinC
    hn hl hr hbefore hsep
  have hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (Set.Subset.refl H)
        (fun v => le_max_left (b v) B) hs) _ _ hpq
  exact ⟨q, hpath, hqn, hq,
    fun side => follow_word_inputs hpq B (fun v => le_max_right (b v) B) side⟩

#print axioms winning_reach_critical_checkpoint
#print axioms winning_reach_critical_checkpoint_above

end Erdos591.Positive.Game.Payoff
