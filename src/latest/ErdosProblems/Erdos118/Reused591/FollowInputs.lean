import ErdosProblems.Erdos118.Reused591.ReachBodyMarker
import ErdosProblems.Erdos118.Reused591.SharedTail

namespace Erdos118.Reused591

/-!
# Coordinate input pools along actual conservative strategy paths

The new coordinates of every reply belong to its finite response input.
Consequently a whole conservative path gives a literal legal coordinate
continuation on the same pool, with any fixed lower bound imposed on the
path's response thresholds. These facts justify the delayed response
inputs used in the shared-prefix and completion constructions.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem follow_step_word_inputs {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N} (h : (exactGame N blue).FollowStep σ H b p q) (side : Bool) :
    ∃ as, LabeledWord.LegalRun (p.position.board.get side) as (q.position.board.get side) ∧
      ∀ a ∈ as, a.2 ∈ H ∧ b p < a.2 := by
  cases h.1 with
  | architect q hp hq =>
      have hnone := ((Concrete.kind_architect_iff (payoff blue) p).mp hp).1
      have hboard := (History.Next.position_next hq).board_eq_of_no_pending hnone
      exact ⟨[], by simpa [hboard] using LabeledWord.LegalRun.nil (p.position.board.get side),
        by simp⟩
  | builder u hp hu huH hub =>
      obtain ⟨r, hpend⟩ := (Concrete.kind_builder_iff (payoff blue) p).mp hp
      have hs := Concrete.response_spec hu
      have hr := hs.reply_spec hpend
      have hpos : ∀ x ∈ u, 0 < x := fun x hx => (Nat.zero_le (b p)).trans_lt (hub x hx)
      obtain ⟨as, has, hmem⟩ := hr.legal_run hpos side
      exact ⟨as, has, fun a ha => ⟨huH (hmem a ha), hub a.2 (hmem a ha)⟩⟩

theorem follow_word_inputs {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N}
    (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    (B : ℕ) (hB : ∀ r, B ≤ b r) (side : Bool) :
    ∃ as, LabeledWord.LegalRun (p.position.board.get side) as (q.position.board.get side) ∧
      ∀ a ∈ as, a.2 ∈ H ∧ B < a.2 := by
  induction h with
  | refl => exact ⟨[], .nil _, by simp⟩
  | @tail q t _ hqt ih =>
      obtain ⟨xs, hx, hxs⟩ := ih
      obtain ⟨ys, hy, hys⟩ := follow_step_word_inputs hqt side
      refine ⟨xs ++ ys, hx.append hy, ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hxs a ha
      · exact ⟨(hys a ha).1, (hB q).trans_lt (hys a ha).2⟩

/-- Extra finite lower bounds may be imposed before continuing a
winning strategy. The resulting path still follows the original strategy. -/
theorem winning_continuation_above {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (B : ℕ) :
    ∃ q : Concrete.Hist N,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ Concrete.done q.position.board = true ∧
      Winning blue (q.position.mode.getD false) q.position.board ∧
      ∀ side, ∃ as,
        LabeledWord.LegalRun (p.position.board.get side) as (q.position.board.get side) ∧
        ∀ a ∈ as, a.2 ∈ H ∧ B < a.2 := by
  let b' : Concrete.Hist N → ℕ := fun r => max (b r) B
  have hwin' := hwin.mono (exactGame N blue) (Set.Subset.refl H)
    (fun r => le_max_left (b r) B)
  obtain ⟨q, hpq, hp, hd, hw⟩ := winning_continuation hHN hH blue hwin'
  have hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (Set.Subset.refl H)
        (fun r => le_max_left (b r) B) hs) _ _ hpq
  exact ⟨q, hpath, hp, hd, hw, fun side =>
    follow_word_inputs hpq B (fun r => le_max_right (b r) B) side⟩

#print axioms follow_word_inputs
#print axioms winning_continuation_above

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
