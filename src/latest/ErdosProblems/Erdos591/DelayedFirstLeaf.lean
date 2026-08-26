import ErdosProblems.Erdos591.BodyPrefixExtension
import ErdosProblems.Erdos591.ReplySeparation

/-!
# Complete a delayed first-leaf response after a retained shorter prefix

The pending label and marker are unchanged. Only the missing leaf
coordinates are chosen now, above a newly issued bound. Their exact
empty-label run extends the virtual prefix and gives one actual reply.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem delayed_first_leaf_from_prefix {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} (σ : (exactGame N blue).ArchitectStrategy)
    (p : Concrete.Hist N) (side : Bool) {B c : ℕ} (L : LastFirstLabels H B 1 c)
    (hp : p.position.pending = some ⟨side, .advance c⟩)
    (hm : (p.position.board.get side).markerEvent = true) {r : ℕ}
    (hparse : (p.position.board.get side).parser = .blocks (r + 1))
    (hB : max p.position.bound (b p) ≤ B) (xs : List ℕ)
    (hshort : xs.length < L.pivot) (hinc : (L.marker :: xs).Pairwise (· < ·))
    (hpool : ∀ x ∈ xs, x ∈ H) (C : ℕ) :
    ∃ q ys, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      (q.position.board.get side).relaxed = true ∧
      q.position.board.get side =
        LabeledWord.bodyLeafCursor (p.position.board.get side) L.upper L.marker r (xs ++ ys) ∧
      (xs ++ ys).length = L.pivot ∧ (L.marker :: (xs ++ ys)).Pairwise (· < ·) ∧
      (∀ y ∈ ys, y ∈ H ∧ C < y) ∧ C < q.position.bound ∧
      LabeledWord.LegalRun
        (LabeledWord.bodyLeafCursor (p.position.board.get side) L.upper L.marker r xs)
        (ys.map fun y => (∅, y)) (q.position.board.get side) ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      ∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  classical
  let D := max C (max L.marker (xs.toFinset.sup id))
  obtain ⟨f, hf, hfH, hfD, _⟩ := FastSequence.exists_above_finite_bounds hH ∅ (fun _ => D)
  let F := (Finset.range (L.pivot - xs.length)).image f
  let ys := F.sort (· ≤ ·)
  have hlen : ys.length = L.pivot - xs.length := by
    simp [ys, F, Finset.card_image_of_injective _ hf.injective]
  have hys : ∀ y ∈ ys, y ∈ H ∧ D < y := by
    intro y hy
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ((Finset.mem_sort (· ≤ ·)).mp hy)
    exact ⟨hfH i, hfD i⟩
  have hfullLen : (xs ++ ys).length = L.pivot := by simp only [List.length_append]; omega
  have hfullInc : (L.marker :: (xs ++ ys)).Pairwise (· < ·) := by
    change ((L.marker :: xs) ++ ys).Pairwise (· < ·)
    apply List.pairwise_append.mpr
    refine ⟨hinc, (Finset.sortedLT_sort F).pairwise, ?_⟩
    intro x hx y hy
    have hxD : x ≤ D := by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (Finset.le_sup (f := id) (List.mem_toFinset.mpr hx)).trans
          ((le_max_right _ _).trans (le_max_right _ _))
    exact hxD.trans_lt (hys y hy).2
  have hfullPool : ∀ x ∈ xs ++ ys, x ∈ H := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hpool x) (fun hy => (hys x hy).1)
  obtain ⟨u, hr, _hsort, huH, huB⟩ := L.leaf_reply p.position.board side r (xs ++ ys)
    ((Position.history_dataInvariant p).2.1 side).1 hparse hm hfullLen hfullInc hfullPool
  obtain ⟨q, hstep, hboard, hn⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp hr huH
    (fun x hx => ⟨((le_max_left _ _).trans hB).trans_lt (huB x hx),
      ((le_max_right _ _).trans hB).trans_lt (huB x hx)⟩)
  have hword : q.position.board.get side =
      LabeledWord.bodyLeafCursor (p.position.board.get side) L.upper L.marker r (xs ++ ys) := by
    simp [hboard]
  have hrel : (q.position.board.get side).relaxed = true := by
    rw [hword]
    simpa [LabeledWord.relaxed, LabeledWord.bodyLeafCursor, LabeledWord.currentLabel, hfullLen]
      using (show 0 < L.pivot ∧ (p.position.board.get side).bodyLabels.length + 1 ∈
        (p.position.board.get side).rootLabel ∧ L.pivot ∈ L.upper from
          ⟨(L.label_bounds.2 _ L.pivot_upper).1, LabeledWord.marker_body_mem hm, L.pivot_upper⟩)
  have hysFresh : ∀ y ∈ ys, y ∈ H ∧ C < y := fun y hy =>
    ⟨(hys y hy).1, (le_max_left _ _).trans_lt (hys y hy).2⟩
  have hysNe : ys ≠ [] := by intro he; simp [he] at hlen; omega
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil ys hysNe
  have hycoords : y ∈ (q.position.board.get side).coordinates := by
    simp only [hword, LabeledWord.bodyLeafCursor, List.mem_append, List.mem_cons]
    exact Or.inr (Or.inr (Or.inr hy))
  have hybound : y ≤ q.position.bound := ((Position.history_dataInvariant q).1 _
    (q.position.board.get_support_subset side (LabeledWord.coordinate_mem_support hycoords))).2.2
  have hraw := LabeledWord.bodyLeafCursor_extend (p.position.board.get side)
    L.upper L.marker r xs ys (by rw [hfullLen]; exact (L.label_bounds.2 _ L.pivot_upper).2.le)
  have hrun : LabeledWord.LegalRun
      (LabeledWord.bodyLeafCursor (p.position.board.get side) L.upper L.marker r xs)
      (ys.map fun y => (∅, y)) (q.position.board.get side) := by
    rw [hword]
    exact LabeledWord.legal_of_zero_atoms hraw
  exact ⟨q, ys, hstep, hn, hrel, hword, hfullLen, hfullInc, hysFresh,
    (hysFresh y hy).2.trans_le hybound, hrun, by simpa [hboard] using hr.other_eq,
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hstep).reply_separation hp⟩

#print axioms delayed_first_leaf_from_prefix

end Erdos591.Positive.Game.Payoff
