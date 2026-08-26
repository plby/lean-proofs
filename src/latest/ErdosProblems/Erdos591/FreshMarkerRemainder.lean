import ErdosProblems.Erdos591.NextMarkerEndpoint

/-!
# Fresh next-marker continuation after an erased singleton-body prefix

A nonempty empty-label run from an exhausted current label is no longer
relaxed. The well-founded first-event parser then reaches exactly the
least future selected root marker, with every new input arbitrarily late.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem NoLeafPending.nonempty_zero_run {w v : LabeledWord} {xs : List ℕ}
    (h : w.NoLeafPending) (hstart : w.parser ≠ .start) (hne : xs ≠ [])
    (hr : w.runAtoms (xs.map fun n => (∅, n)) = some v) :
    v.NoLeafPending ∧ v.relaxed = false := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons n xs =>
      cases hread : w.read ∅ n with
      | none => simp [runAtoms, hread] at hr
      | some first =>
          have htail : first.runAtoms (xs.map fun n => (∅, n)) = some v := by
            simpa [runAtoms, hread] using hr
          have hf := h.read hstart hread
          exact hf.1.zero_run (read_parser_ne_start hread) hf.2 htail

theorem fresh_next_marker_remainder {H : Set ℕ} (hH : H.Infinite) (w : LabeledWord)
    (hw : w.CursorInvariant) (hstart : w.parser ≠ .start)
    (hn : w.NoLeafPending) (hrel : w.relaxed = false) {i : ℕ}
    (hi : BeforeBody i w)
    (hnext : ∀ k ∈ w.rootLabel, w.bodyLabels.length < k → i ≤ k) (C : ℕ) :
    ∃ xs : List ℕ, ∃ v, LegalRun w (xs.map fun n => (∅, n)) v ∧
      v.markerEvent = true ∧ v.bodyLabels.length + 1 = i ∧
      xs.Pairwise (· < ·) ∧ (∀ x ∈ xs, x ∈ H ∧ C < x) ∧
      (∀ x ∈ w.coordinates, ∀ y ∈ xs, x < y) := by
  let D := max C (w.coordinates.toFinset.sup id)
  let J := H \ Set.Iic D
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic D)
  obtain ⟨u, ⟨v, hrun⟩, huJ⟩ := advanceRemainder.family_exists w hJ
  have hvalues : ∀ x ∈ u.sort (· ≤ ·), x ∈ H ∧ D < x := by
    intro x hx
    have hu := huJ ((Finset.mem_sort (· ≤ ·)).mp hx)
    exact ⟨hu.1, lt_of_not_ge hu.2⟩
  obtain ⟨hm, hidx⟩ := hn.remainder_marker hw hstart hrel hi le_rfl hnext hrun
  refine ⟨u.sort (· ≤ ·), v, zero_run_legal _ (fun _ _ => rfl) hrun,
    hm, hidx, (Finset.sortedLT_sort u).pairwise, ?_, ?_⟩
  · exact fun x hx => ⟨(hvalues x hx).1, (le_max_left _ _).trans_lt (hvalues x hx).2⟩
  · intro x hx y hy
    exact ((Finset.le_sup (f := id) (List.mem_toFinset.mpr hx)).trans
      (le_max_right _ _)).trans_lt (hvalues y hy).2

#print axioms NoLeafPending.nonempty_zero_run
#print axioms fresh_next_marker_remainder

end Erdos591.Positive.Game.LabeledWord
