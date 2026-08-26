import ErdosProblems.Erdos118.Reused591.SameBodyRun

namespace Erdos118.Reused591

/-!
# Acceptance at the next selected leaf after an earlier selected leaf

Past label indices are retained. Once the current leaf index has passed
the old selected index, assume the next possible selected index is `j`.
Any first-event prefix bounded by `j` must end exactly at `j`. Equal
parser counters then force the whole prescribed prefix to be accepted.
-/

namespace Erdos591.Positive.Game.LabeledWord

namespace UpToLeaf

theorem at_event {j : ℕ} {w : LabeledWord} (h : UpToLeaf j w)
    (hw : w.CursorInvariant) (he : w.event = true) : w.relaxed = true := by
  obtain ⟨r, k, hp⟩ := h.parser_leaves hw
  simpa [event, terminal, markerEvent, hp] using he

theorem parser_eq {j : ℕ} {u v : LabeledWord} (hu : UpToLeaf j u) (hv : UpToLeaf j v)
    (hcu : u.CursorInvariant) (hcv : v.CursorInvariant)
    (hcount : u.bodyLabels.length = v.bodyLabels.length) (hroot : u.rootMarker = v.rootMarker)
    (hleaf : u.leafIndex = v.leafIndex) (hbody : u.bodyMarker = v.bodyMarker) :
    u.parser = v.parser := by
  obtain ⟨r, k, huparse⟩ := hu.parser_leaves hcu
  obtain ⟨s, l, hvparse⟩ := hv.parser_leaves hcv
  have hc₁ := hcu.2.1
  have hc₂ := hcv.2.1
  simp only [Counters, huparse, hvparse, outstandingBodies, outstandingLeaves] at hc₁ hc₂
  have hrs : r = s := by omega
  have hkl : k = l := by omega
  rw [huparse, hvparse, hrs, hkl]

end UpToLeaf

theorem advanceRemainder_to_next_leaf {w v : LabeledWord} {xs : List ℕ} {i j : ℕ}
    (hw : w.CursorInvariant) (hs : UpToLeaf j w) (hafter : i < w.leafIndex)
    (hnext : ∀ k ∈ w.currentLabel, i < k → j ≤ k)
    (hraw : w.runAtoms (xs.map fun n => (∅, n)) = some v)
    (hvs : UpToLeaf j v) (hvleaf : v.leafIndex = j)
    (hlabels : v.bodyLabels = w.bodyLabels) (hbody : v.bodyMarker = w.bodyMarker) :
    advanceRemainder.run w xs = some v := by
  have hstart : w.parser ≠ .start := by
    obtain ⟨r, k, hp⟩ := hs.parser_leaves hw
    simp [hp]
  have hlv := legal_of_zero_atoms hraw
  have hv := hvs.relaxed_of_eq (hlv.cursorInvariant hw) hvleaf
  apply response_eq_of_endpoint_parser advanceRemainder (fun _ _ => rfl) hraw
    (by simp [advanceRemainder, event, hv])
  intro _front _tail u _hxs hf _ht
  have hlu := zero_run_legal advanceRemainder (fun _ _ => rfl) hf
  have hu := hs.remainder hw hf
  have hcu := hlu.cursorInvariant hw
  have hur := hu.1.at_event hcu (advanceRemainder.run_stopped hf)
  have hcount := hlu.leafIndex_of_body_length hstart (congrArg List.length hu.2.1)
  have hau : i < u.leafIndex := by omega
  have hmem : u.leafIndex ∈ w.currentLabel := by
    have hm : 0 < u.leafIndex ∧ u.bodyLabels.length ∈ u.rootLabel ∧
        u.leafIndex ∈ u.currentLabel := by simpa [relaxed] using hur
    simpa [currentLabel, hu.2.1] using hm.2.2
  have hleaf : u.leafIndex = j := le_antisymm hu.1.before (hnext _ hmem hau)
  exact hu.1.parser_eq hvs hcu (hlv.cursorInvariant hw)
    (congrArg List.length (hu.2.1.trans hlabels.symm))
    ((hlu.rootMarker_eq hstart).trans (hlv.rootMarker_eq hstart).symm)
    (hleaf.trans hvleaf.symm) (hu.2.2.trans hbody.symm)

#print axioms advanceRemainder_to_next_leaf

end Erdos591.Positive.Game.LabeledWord

end Erdos118.Reused591
