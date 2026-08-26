import ErdosProblems.Erdos591.ReservedOpening
import ErdosProblems.Erdos591.RootGluingHistory

/-!
# The actual next body request after a reserved opening

Submit the reconstructed initial response to its saved winning history,
then obtain the strategy's positive request at the first selected body.
The fresh coordinate tail starts at the virtual relabeling of the old
prefix, so it can later be concatenated with actual fine-history moves.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_reserved_root_request {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool) {c : ℕ}
    (hp : p.position.pending = some ⟨side, .advance c⟩)
    (hinit : p.position.board.get side = LabeledWord.initial)
    {D C : Finset ℕ} {n B : ℕ} {as : List (Finset ℕ × ℕ)} {w : LabeledWord}
    (hraw : (LabeledCode.rootCursor D n).runAtoms as = some w)
    (hC : ∀ x ∈ C, x ∈ H ∧ B < x ∧ x < n) (hn : n ∈ H ∧ B < n)
    (hcard : C.card = c) (hCne : C.Nonempty)
    (hbefore : ∀ i ∈ C, w.bodyLabels.length < i)
    (hinc : (n :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H)
    (hB : max p.position.bound (b p) ≤ B) (K : ℕ) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨side, .advance d⟩ ∧ 0 < d ∧
      (q.position.board.get side).markerEvent = true ∧
      (q.position.board.get side).NoRootPassed ∧ (q.position.board.get side).rootLabel = C ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      ∃ tail, LabeledWord.LegalRun (LabeledWord.rootRelabel C w)
        (tail.map fun n => (∅, n)) (q.position.board.get side) ∧
        (∀ x ∈ tail, x ∈ H ∧ K < x) ∧
        (q.position.board.get side).coordinates = w.coordinates ++ tail := by
  obtain ⟨u, last, tail, hr, huH, huB, hrun, htail, hm, hno, hroot, hcoords⟩ :=
    Reply.reserved_root_exists_run hH p.position.board side hinit
      hraw hC hn hCne hbefore hinc hpool K
  rw [hcard] at hr
  obtain ⟨v, hs, hboard, hvn⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp hr huH
    (fun x hx => ⟨((le_max_left _ _).trans hB).trans_lt (huB x hx),
      ((le_max_right _ _).trans hB).trans_lt (huB x hx)⟩)
  have hword : v.position.board.get side = last := by simp [hboard]
  have hwinv := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
  obtain ⟨q, d, hrequest, hboard', hpend, hd⟩ := winning_request_at_marker hHN hH blue
    hwinv side hvn (by simpa only [hword] using hm)
  have hwordq : q.position.board.get side = last := by simpa only [hboard'] using hword
  refine ⟨q, d, (Relation.ReflTransGen.single hs).tail hrequest, hpend, hd,
    by simpa only [hwordq] using hm, by simpa only [hwordq] using hno,
    by simpa only [hwordq] using hroot, ?_, tail,
    by simpa only [hwordq] using hrun, htail, by simpa only [hwordq] using hcoords⟩
  simpa [hboard', hboard] using hr.other_eq

#print axioms winning_reserved_root_request

end Erdos591.Positive.Game.Payoff
