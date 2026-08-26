import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory

namespace Erdos118.Reused591

/-!
# An actual body reply with a prescribed nonempty full label

View the minimum of the prescribed label as a singleton lower label.
The checked first-leaf response supplies the full issued label, its
common marker, and the canonical increasing coordinate prefix. The
opposite word is unchanged, and no winning or future-size premise is
needed to construct this one legal reply.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem prescribed_body_opening {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy) (p : Concrete.Hist N) (side : Bool)
    {B c marker : ℕ} (D : Finset ℕ) (hne : D.Nonempty) (hcard : D.card = c)
    (hD : ∀ x ∈ D, x ∈ H ∧ B < x ∧ x < marker)
    (hmarker : marker ∈ H ∧ B < marker)
    (hp : p.position.pending = some ⟨side, .advance c⟩)
    (hm : (p.position.board.get side).markerEvent = true)
    (hB : max p.position.bound (b p) ≤ B) :
    ∃ q, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).rootLabel = (p.position.board.get side).rootLabel ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ++ [D] ∧
      (q.position.board.get side).currentLabel = D ∧
      (q.position.board.get side).leafIndex = D.min' hne ∧
      (q.position.board.get side).bodyMarker = marker ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      ∃ r xs, (p.position.board.get side).parser = .blocks (r + 1) ∧
        (q.position.board.get side) =
          LabeledWord.bodyLeafCursor (p.position.board.get side) D marker r xs ∧
        xs.length = D.min' hne ∧ (marker :: xs).Pairwise (· < ·) ∧
        ∀ x ∈ xs, x ∈ H ∧ marker < x := by
  classical
  let V : LastFirstLabels H B 1 c := {
    lower := {D.min' hne}
    upper := D
    pivot := D.min' hne
    marker := marker
    lower_card := by simp
    upper_card := hcard
    pivot_lower := by simp
    pivot_upper := D.min'_mem hne
    lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
    upper_ge := fun x hx => D.min'_le x hx
    lower_fresh := by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact hD _ (D.min'_mem hne)
    upper_fresh := hD
    marker_fresh := hmarker }
  obtain ⟨q, _v, hpq, _hpv, hqn, _hvn, _hshape, hqr, _hvr, hqi, _hvi, hqb, _hvb,
      hqo, _hvo, r, xs, hparse, hword, _hwordv, hlen, hinc, hpool⟩ :=
    first_leaf_gluing_prefix hHN hH blue σ p p side side V V rfl rfl hp hp hm hm
      (LabeledWord.SameStructure.refl _) hB hB
  change q.position.board.get side =
    LabeledWord.bodyLeafCursor (p.position.board.get side) D marker r xs at hword
  refine ⟨q, hpq, hqn, hqr, ?_, hqb, ?_, hqi, ?_, hqo,
    r, xs, hparse, hword, hlen, hinc, hpool⟩
  · simp only [hword, LabeledWord.bodyLeafCursor]
  · simp [LabeledWord.currentLabel, hqb, V]
  · simp only [hword, LabeledWord.bodyLeafCursor]

#print axioms prescribed_body_opening

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
