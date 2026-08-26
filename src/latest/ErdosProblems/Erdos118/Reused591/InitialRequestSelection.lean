import ErdosProblems.Erdos118.Reused591.OutsideBoundary

namespace Erdos118.Reused591

/-!
# Initial requests and unread selections in the opposite word

A zero-size initial reply completes its word, so it is impossible while
the opposite word still has an unread selection. Conversely, when the
initial word is the smaller-endpoint word and the opposite word has
exhausted its selections, its initial request must have size zero.
These facts supply the zero/positive branches of the inside construction
without assuming a count of cuts in a completed pair.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff

theorem Reply.initial_positive_marker {board last : Board} {side : Bool} {d : ℕ}
    {u : Finset ℕ} (hr : Reply board ⟨side, .advance d⟩ u last)
    (hinit : board.get side = LabeledWord.initial) (hd : 0 < d)
    (hpos : ∀ x ∈ u, 0 < x) : (last.get side).markerEvent = true := by
  cases hr with
  | advance side d u w hlegal hrun =>
      have hrun' : Advance.parser.run (.prelude ⟨LabeledWord.initial, rfl⟩ d [])
          (u.sort (· ≤ ·)) = some (.remainder w) := by simpa only [hinit] using hrun
      simpa using Advance.initial_positive_marker d hd (u.sort (· ≤ ·)) w
        (Finset.sortedLT_sort u).pairwise
        (fun x hx => hpos x ((Finset.mem_sort (· ≤ ·)).mp hx)) hrun'

namespace Payoff

theorem winning_initial_positive_of_other_pending {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r)
    (hinit : p.position.board.get r.side = LabeledWord.initial)
    (hother : Macro.Pending (p.position.board.get (!r.side))) : 0 < r.size := by
  by_contra hn
  have hz : r.size = 0 := by omega
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hs : (exactGame N blue).FollowStep σ H b p (Concrete.response p u) :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hwinq := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
  have hr := (Concrete.response_spec hu).reply_spec hp
  have ht := hr.size_zero_terminal (by simp [hinit, LabeledWord.initial]) hz
  have hnot := winning_not_pending_of_other_complete hHN hH blue hwinq (!r.side)
    (by simpa using ht)
  rw [hr.other_eq] at hnot
  exact hnot hother

theorem winning_initial_smaller_zero_of_other_last {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} {mode : Bool}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some mode) {r : Request}
    (hp : p.position.pending = some r) (hside : r.side = mode)
    (hinit : p.position.board.get r.side = LabeledWord.initial)
    (hstart : (p.position.board.get (!mode)).parser ≠ .start)
    (hn : ¬ Macro.Pending (p.position.board.get (!mode))) : r.size = 0 := by
  by_contra hz
  have hpos : 0 < r.size := Nat.pos_of_ne_zero hz
  obtain ⟨d, hd, heq⟩ : ∃ d, 0 < d ∧ r = ⟨mode, .advance d⟩ := by
    cases r with
    | mk side command =>
        cases command with
        | finish => simp [Request.size] at hpos
        | advance d =>
            exact ⟨d, hpos, by simpa using congrArg (fun s => Request.mk s (.advance d)) hside⟩
  subst r
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hs : (exactGame N blue).FollowStep σ H b p (Concrete.response p u) :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hpath := Relation.ReflTransGen.single hs
  have hwinq := hwin.of_reachable (exactGame N blue) hpath
  have hr := (Concrete.response_spec hu).reply_spec hp
  have hm := hr.initial_positive_marker hinit hd
    (fun x hx => (Nat.zero_le (b p)).trans_lt (hub x hx))
  obtain ⟨k, hparse⟩ := LabeledWord.marker_blocks hm
  have hsmallStart : ((Concrete.response p u).position.board.get mode).parser ≠ .start := by
    simp [hparse]
  have hlargeStart : ((Concrete.response p u).position.board.get (!mode)).parser ≠ .start := by
    simpa using hr.other_eq.symm ▸ hstart
  have hlargeLast : ¬ Macro.Pending ((Concrete.response p u).position.board.get (!mode)) := by
    simpa using hr.other_eq.symm ▸ hn
  exact (winning_no_pending_smaller hHN hH blue hwinq (follow_mode_some hpath hmode)
    hsmallStart hlargeStart hlargeLast) (Macro.marker_pending hm)

#print axioms winning_initial_positive_of_other_pending
#print axioms winning_initial_smaller_zero_of_other_last

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
