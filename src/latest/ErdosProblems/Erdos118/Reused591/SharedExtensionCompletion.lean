import ErdosProblems.Erdos118.Reused591.BoundaryRequests

namespace Erdos118.Reused591

/-!
# One complete response shared with an older pending extension

The newer play may already have extended the common starting prefix.
Those recorded coordinates are combined with one sufficiently late
complete response. The full coordinate continuation is then submitted
as the older play's pending complete response. Both opposite words
remain unchanged, and both moves follow the original strategy.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem complete_shared_extension {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (old p : Concrete.Hist N)
    {oldRequest r : Request} (hold : old.position.pending = some oldRequest)
    (hp : p.position.pending = some r)
    (holdStart : (old.position.board.get oldRequest.side).parser ≠ .start)
    (holdLast : ¬ Macro.Pending (old.position.board.get oldRequest.side))
    (hpStart : (p.position.board.get r.side).parser ≠ .start)
    (hpLast : ¬ Macro.Pending (p.position.board.get r.side))
    {before : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (hsame : LabeledWord.SameStructure (old.position.board.get oldRequest.side) before)
    (hbefore : LabeledWord.LegalRun before xs (p.position.board.get r.side))
    (hbeforePool : ∀ a ∈ xs, a.2 ∈ H ∧ old.position.bound < a.2 ∧ b old < a.2) :
    ∃ old' p', (exactGame N blue).FollowStep σ H b old old' ∧
      (exactGame N blue).FollowStep σ H b p p' ∧
      old'.position.pending = none ∧ p'.position.pending = none ∧
      (p'.position.board.get r.side).terminal = true ∧
      LabeledWord.SameStructure (old'.position.board.get oldRequest.side)
        (p'.position.board.get r.side) ∧
      old'.position.board.get (!oldRequest.side) = old.position.board.get (!oldRequest.side) ∧
      p'.position.board.get (!r.side) = p.position.board.get (!r.side) := by
  let C := max (b p) (max old.position.bound (b old))
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, huC⟩ := (exactGame N blue).response_exists_above hHN hH p hk C
  let p' := Concrete.response p u
  have hs : (exactGame N blue).FollowStep σ H b p p' :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH
      (fun x hx => (le_max_left _ _).trans_lt (huC x hx))
  have hr := (Concrete.response_spec hu).reply_spec hp
  have hf := (Reply.not_pending_iff_finish p.position.board r u p'.position.board
    ((Position.history_controlInvariant p).2 r hp) hpStart hpLast).mp hr
  have ht := hf.finish_terminal
  obtain ⟨ys, hy, hymem⟩ := hr.legal_run
    (fun x hx => (Nat.zero_le C).trans_lt (huC x hx)) r.side
  have hrun := hbefore.append hy
  have hpool : ∀ a ∈ xs ++ ys,
      a.2 ∈ H ∧ old.position.bound < a.2 ∧ b old < a.2 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hbeforePool a ha
    · have hbig := (le_max_right (b p) _).trans_lt (huC a.2 (hymem a ha))
      exact ⟨huH (hymem a ha), (le_max_left _ _).trans_lt hbig,
        (le_max_right _ _).trans_lt hbig⟩
  have hinc : ((xs ++ ys).map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant p').2.1 r.side).2
    rw [LabeledWord.runAtoms_coordinates hrun.run] at hi
    exact (List.pairwise_append.mp hi).2.1
  obtain ⟨old', ho, hon, he, hother⟩ := Concrete.follow_shared_tail hHN (payoff blue) σ
    old hold holdStart holdLast hsame hrun.run ht hinc hpool
  exact ⟨old', p', ho, hs, hon,
    (History.Next.position_next (FiniteResponseGame.FollowStep.next
      (exactGame N blue) hs)).no_pending_after_reply hp, ht, he, hother, hr.other_eq⟩

#print axioms complete_shared_extension

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
