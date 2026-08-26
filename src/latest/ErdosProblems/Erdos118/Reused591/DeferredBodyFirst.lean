import ErdosProblems.Erdos118.Reused591.PrescribedBodyOpening
import ErdosProblems.Erdos118.Reused591.BodyPrefixExtension

namespace Erdos118.Reused591

/-!
# Complete a saved first-body response after an already recorded prefix

The old label, marker and partial leaf prefix retain their original
bound and pool. Append only the missing leaf coordinates on a smaller
future pool above a new bound, then submit the full first-leaf reply.
The newly appended tail is retained for the other pending play.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem deferred_body_first_from_prefix {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} (σ : (exactGame N blue).ArchitectStrategy)
    (p : Concrete.Hist N) (side : Bool) {B c marker k : ℕ}
    (D : Finset ℕ) (hne : D.Nonempty) (hcard : D.card = c)
    (hD : ∀ x ∈ D, x ∈ H ∧ B < x ∧ x < marker)
    (hmarker : marker ∈ H ∧ B < marker)
    (hp : p.position.pending = some ⟨side, .advance c⟩)
    (hm : (p.position.board.get side).markerEvent = true)
    (hparse : (p.position.board.get side).parser = .blocks (k + 1))
    (hB : max p.position.bound (b p) ≤ B)
    (xs : List ℕ) (hinc : (marker :: xs).Pairwise (· < ·))
    (hpool : ∀ x ∈ xs, x ∈ H) (hbefore : xs.length < D.min' hne) (C : ℕ) :
    ∃ q ys, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).rootLabel = (p.position.board.get side).rootLabel ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ++ [D] ∧
      (q.position.board.get side).currentLabel = D ∧
      (q.position.board.get side).leafIndex = D.min' hne ∧
      (q.position.board.get side).bodyMarker = marker ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      (∀ x ∈ (q.position.board.get (!side)).coordinates,
        x ≤ (q.position.board.get side).coordinates.getLastD 0) ∧
      (q.position.board.get side) =
        LabeledWord.bodyLeafCursor (p.position.board.get side) D marker k (xs ++ ys) ∧
      LabeledWord.LegalRun (LabeledWord.bodyLeafCursor (p.position.board.get side) D marker k xs)
        (ys.map fun y => (∅, y)) (q.position.board.get side) ∧
      ys.length = D.min' hne - xs.length ∧
      (marker :: (xs ++ ys)).Pairwise (· < ·) ∧
      ∀ y ∈ ys, y ∈ K ∧ C < y := by
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
  let Z := max C (max marker (xs.toFinset.sup id))
  obtain ⟨f, hf, hfK, hfZ, _⟩ := FastSequence.exists_above_finite_bounds hK ∅ (fun _ => Z)
  let E := (Finset.range (D.min' hne - xs.length)).image f
  let ys := E.sort (· ≤ ·)
  have hlen : ys.length = D.min' hne - xs.length := by
    simp [ys, E, Finset.card_image_of_injective _ hf.injective]
  have hys : ∀ y ∈ ys, y ∈ K ∧ Z < y := by
    intro y hy
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ((Finset.mem_sort (· ≤ ·)).mp hy)
    exact ⟨hfK i, hfZ i⟩
  have hsep : ∀ x ∈ marker :: xs, ∀ y ∈ ys, x < y := by
    intro x hx y hy
    have hxZ : x ≤ Z := by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (Finset.le_sup (f := id) (List.mem_toFinset.mpr hx)).trans
          ((le_max_right _ _).trans (le_max_right _ _))
    exact hxZ.trans_lt (hys y hy).2
  have hfullInc : (marker :: (xs ++ ys)).Pairwise (· < ·) := by
    simpa only [List.cons_append] using
      List.pairwise_append.mpr ⟨hinc, (Finset.sortedLT_sort E).pairwise, hsep⟩
  have hfullLen : (xs ++ ys).length = D.min' hne := by
    simp only [List.length_append, hlen]
    omega
  obtain ⟨u, hreply, _hsort, huH, huB⟩ := V.leaf_reply p.position.board side k (xs ++ ys)
    ((Position.history_dataInvariant p).2.1 side).1 hparse hm hfullLen hfullInc (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpool x hx
      · exact hKH (hys x hx).1)
  obtain ⟨q, hpq, hboard, hqn⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp hreply huH
    (fun x hx => ⟨((le_max_left _ _).trans hB).trans_lt (huB x hx),
      ((le_max_right _ _).trans hB).trans_lt (huB x hx)⟩)
  have hword : q.position.board.get side =
      LabeledWord.bodyLeafCursor (p.position.board.get side) D marker k (xs ++ ys) := by
    simp [hboard, V]
  have hrel : (q.position.board.get side).relaxed = true := by
    rw [hword]
    simpa [LabeledWord.relaxed, LabeledWord.bodyLeafCursor, LabeledWord.currentLabel,
      hfullLen] using (show 0 < D.min' hne ∧
        (p.position.board.get side).bodyLabels.length + 1 ∈
          (p.position.board.get side).rootLabel ∧ D.min' hne ∈ D from
      ⟨(Nat.zero_le B).trans_lt (hD _ (D.min'_mem hne)).2.1,
        LabeledWord.marker_body_mem hm, D.min'_mem hne⟩)
  have htail := LabeledWord.bodyLeafCursor_extend (p.position.board.get side) D marker k xs ys
    (by rw [hfullLen]; exact (hD _ (D.min'_mem hne)).2.2.le)
  refine ⟨q, ys, hpq, hqn, hrel, ?_, ?_, ?_, ?_, ?_, ?_,
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hpq).reply_separation hp,
    hword, ?_, hlen, hfullInc, ?_⟩
  · simp only [hword, LabeledWord.bodyLeafCursor]
  · simp only [hword, LabeledWord.bodyLeafCursor]
  · simp [hword, LabeledWord.bodyLeafCursor, LabeledWord.currentLabel]
  · simpa only [hword, LabeledWord.bodyLeafCursor] using hfullLen
  · simp only [hword, LabeledWord.bodyLeafCursor]
  · simpa [hboard] using hreply.other_eq
  · rw [hword]
    exact LabeledWord.legal_of_zero_atoms htail
  · intro y hy
    exact ⟨(hys y hy).1, (le_max_left _ _).trans_lt (hys y hy).2⟩

#print axioms deferred_body_first_from_prefix

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
