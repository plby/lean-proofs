import ErdosProblems.Erdos591.MarkerPrefixAcceptance
import ErdosProblems.Erdos591.FirstLeafResponse

/-!
# Acceptance of a prescribed first-leaf prefix

A literal leaf prefix ending at the least selected index is the actual
first-event response. Accepted prefixes preserve the body labels and
marker. Their equal least index gives equal parser counters, so the
strict parser potential again excludes any remaining atomic tail.
-/

namespace Erdos591.Positive.Game.LabeledWord

namespace FirstLeafState

theorem remainder_bodyMarker {w v : LabeledWord} {xs : List ℕ}
    (h : w.FirstLeafState) (hw : w.CursorInvariant)
    (hrun : advanceRemainder.run w xs = some v) : v.bodyMarker = w.bodyMarker := by
  induction xs generalizing w with
  | nil =>
      cases he : w.event with
      | false => simp [ResponseParser.run, advanceRemainder, he] at hrun
      | true =>
          have heq : w = v := by simpa [ResponseParser.run, advanceRemainder, he] using hrun
          exact congrArg LabeledWord.bodyMarker heq.symm
  | cons n xs ih =>
      cases he : w.event with
      | true => simp [ResponseParser.run, advanceRemainder, he] at hrun
      | false =>
          obtain ⟨u, hu⟩ := read_exists (event_false_terminal he) ∅ n
          have ht : advanceRemainder.run u xs = some v := by
            simpa [ResponseParser.run, advanceRemainder, he, hu] using hrun
          have hv := ih (h.read hw he hu) (hw.read (allowed_empty (read_nonterminal hu) n) hu) ht
          obtain ⟨r, k, hp⟩ := h.parser_leaves hw
          have heq : w.record ∅ n (Parser.normalize r k) = u := by
            simpa [LabeledWord.read, hp, Parser.step] using hu
          rw [hv, ← heq]
          simp [record, hp]

theorem leafIndex_eq {u v : LabeledWord} (hu : u.FirstLeafState) (hv : v.FirstLeafState)
    (hru : u.relaxed = true) (hrv : v.relaxed = true)
    (hlabels : u.bodyLabels = v.bodyLabels) : u.leafIndex = v.leafIndex := by
  have hmu : u.leafIndex ∈ u.currentLabel := by
    have h : 0 < u.leafIndex ∧ u.bodyLabels.length ∈ u.rootLabel ∧
        u.leafIndex ∈ u.currentLabel := by simpa [relaxed] using hru
    exact h.2.2
  have hmv : v.leafIndex ∈ v.currentLabel := by
    have h : 0 < v.leafIndex ∧ v.bodyLabels.length ∈ v.rootLabel ∧
        v.leafIndex ∈ v.currentLabel := by simpa [relaxed] using hrv
    exact h.2.2
  have hcurrent : u.currentLabel = v.currentLabel := by simp [currentLabel, hlabels]
  exact le_antisymm (hu.before _ (hcurrent ▸ hmv)) (hv.before _ (hcurrent ▸ hmu))

theorem parser_eq {u v : LabeledWord} (hu : u.FirstLeafState) (hv : v.FirstLeafState)
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

end FirstLeafState

theorem advanceRemainder_to_first_leaf {w v : LabeledWord} {xs : List ℕ}
    (hw : w.CursorInvariant) (hs : w.FirstLeafState)
    (hraw : w.runAtoms (xs.map fun n => (∅, n)) = some v)
    (hv : v.relaxed = true) (hvs : v.FirstLeafState)
    (hlabels : v.bodyLabels = w.bodyLabels) (hbody : v.bodyMarker = w.bodyMarker) :
    advanceRemainder.run w xs = some v := by
  have hstart : w.parser ≠ .start := by
    obtain ⟨r, k, hp⟩ := hs.parser_leaves hw
    simp [hp]
  apply response_eq_of_endpoint_parser advanceRemainder (fun _ _ => rfl) hraw
    (by simp [advanceRemainder, event, hv])
  intro _front _tail u _hxs hf _ht
  have hlu := zero_run_legal advanceRemainder (fun _ _ => rfl) hf
  have hlv := legal_of_zero_atoms hraw
  have hus := hs.remainder hw hf
  have hur := (hs.remainder_minimum hw hf).1
  have hsameLabels : u.bodyLabels = v.bodyLabels :=
    (hs.remainder_bodyLabels hw hf).trans hlabels.symm
  have hleaf := hus.leafIndex_eq hvs hur hv hsameLabels
  exact hus.parser_eq hvs (hlu.cursorInvariant hw) (hlv.cursorInvariant hw)
    (congrArg List.length hsameLabels)
    ((hlu.rootMarker_eq hstart).trans (hlv.rootMarker_eq hstart).symm) hleaf
    ((hs.remainder_bodyMarker hw hf).trans hbody.symm)

#print axioms advanceRemainder_to_first_leaf

end Erdos591.Positive.Game.LabeledWord
