import ErdosProblems.Erdos118.Reused591.SharedTailHistory

namespace Erdos118.Reused591

/-!
# Simultaneous complete responses with already recorded fresh prefixes

Each old complete response may already have a legal coordinate prefix
inside the later winning play. Retain its virtual starting cursor, then
append one sufficiently late common completion and replay every old tail.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_shared_completions_from_prefixes {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p) (m : ℕ)
    (old : Fin m → Concrete.Hist N) (r : Fin m → Request) (side : Fin m → Bool)
    (hp : ∀ k, (old k).position.pending = some (r k))
    (hstart : ∀ k, ((old k).position.board.get (r k).side).parser ≠ .start)
    (hlast : ∀ k, ¬ Macro.Pending ((old k).position.board.get (r k).side))
    (hprefix : ∀ k, ∃ anchor,
      LabeledWord.SameStructure ((old k).position.board.get (r k).side) anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as (p.position.board.get (side k)) ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max (old k).position.bound (b (old k)) < a.2) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      Concrete.done q.position.board = true ∧
      Winning blue (q.position.mode.getD false) q.position.board ∧
      ∀ k, ∃ old', (exactGame N blue).FollowStep σ H b (old k) old' ∧
        old'.position.pending = none ∧
        LabeledWord.SameStructure (old'.position.board.get (r k).side)
          (q.position.board.get (side k)) ∧
        old'.position.board.get (!(r k).side) = (old k).position.board.get (!(r k).side) := by
  let B := Finset.univ.sup (fun k : Fin m => max (old k).position.bound (b (old k)))
  obtain ⟨q, hpath, _hqn, hdone, hwinning, hwords⟩ := winning_continuation_above hHN hH blue hwin B
  refine ⟨q, hpath, hdone, hwinning, ?_⟩
  intro k
  obtain ⟨anchor, hsame, frontAtoms, hfront, hfreshFront⟩ := hprefix k
  obtain ⟨as, has, hinputs⟩ := hwords (side k)
  have hwhole := hfront.append has
  have hB : max (old k).position.bound (b (old k)) ≤ B :=
    Finset.le_sup (f := fun k : Fin m => max (old k).position.bound (b (old k)))
      (Finset.mem_univ k)
  have hinc : ((frontAtoms ++ as).map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant q).2.1 (side k)).2
    rw [LabeledWord.runAtoms_coordinates hwhole.run] at hi
    exact (List.pairwise_append.mp hi).2.1
  have hpool : ∀ a ∈ frontAtoms ++ as,
      a.2 ∈ H ∧ (old k).position.bound < a.2 ∧ b (old k) < a.2 := by
    intro a ha
    have hf : a.2 ∈ H ∧ max (old k).position.bound (b (old k)) < a.2 := by
      rcases List.mem_append.mp ha with ha | ha
      · exact hfreshFront a ha
      · exact ⟨(hinputs a ha).1, hB.trans_lt (hinputs a ha).2⟩
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2, (le_max_right _ _).trans_lt hf.2⟩
  exact Concrete.follow_shared_tail hHN (payoff blue) σ (old k) (hp k) (hstart k)
    (hlast k) hsame hwhole.run (q.position.board.terminal_of_done hdone (side k)) hinc hpool

#print axioms winning_shared_completions_from_prefixes

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
