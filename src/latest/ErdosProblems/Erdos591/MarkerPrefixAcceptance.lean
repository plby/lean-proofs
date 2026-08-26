import ErdosProblems.Erdos591.EventPrefix
import ErdosProblems.Erdos591.FirstMarkerIndex

/-!
# Acceptance of a prescribed first-marker prefix

An empty-body-label atomic prefix ending at the least selected body
marker is the actual first-event response. Any earlier accepted prefix
would end at the same least index and have the same parser state;
strict decrease then forces the alleged intervening tail to be empty.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem read_rootMarker_eq {w v : LabeledWord} {D : Finset ℕ} {n : ℕ}
    (hr : w.read D n = some v) (hw : w.parser ≠ .start) : v.rootMarker = w.rootMarker := by
  cases hs : Parser.step w.parser n with
  | none => simp [LabeledWord.read, hs] at hr
  | some p =>
      have heq : w.record D n p = v := by simpa [LabeledWord.read, hs] using hr
      subst v
      cases hp : w.parser <;> simp_all [record]

theorem LegalRun.rootMarker_eq {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hw : w.parser ≠ .start) : v.rootMarker = w.rootMarker := by
  induction h with
  | nil => rfl
  | cons w D n u xs v _ hr _ ih =>
      exact (ih (read_parser_ne_start hr)).trans (read_rootMarker_eq hr hw)

theorem marker_blocks {w : LabeledWord} (hm : w.markerEvent = true) :
    ∃ r, w.parser = .blocks (r + 1) := by
  cases hp : w.parser with
  | start => simp [markerEvent, hp] at hm
  | leaves r k => simp [markerEvent, hp] at hm
  | blocks r =>
      cases r with
      | zero => simp [markerEvent, hp] at hm
      | succ r => exact ⟨r, rfl⟩

theorem marker_body_mem {w : LabeledWord} (hm : w.markerEvent = true) :
    w.bodyLabels.length + 1 ∈ w.rootLabel := by
  obtain ⟨r, hp⟩ := marker_blocks hm
  simpa [markerEvent, hp] using hm

theorem NoRootPassed.body_length_eq {u v : LabeledWord} (hu : u.NoRootPassed)
    (hv : v.NoRootPassed) (hmu : u.markerEvent = true) (hmv : v.markerEvent = true)
    (hroot : u.rootLabel = v.rootLabel) : u.bodyLabels.length = v.bodyLabels.length := by
  have h₁ := hu _ (by rw [hroot]; exact marker_body_mem hmv)
  have h₂ := hv _ (by rw [← hroot]; exact marker_body_mem hmu)
  omega

theorem marker_parser_eq {u v : LabeledWord} (hu : u.CursorInvariant) (hv : v.CursorInvariant)
    (hmu : u.markerEvent = true) (hmv : v.markerEvent = true)
    (hcount : u.bodyLabels.length = v.bodyLabels.length) (hm : u.rootMarker = v.rootMarker) :
    u.parser = v.parser := by
  obtain ⟨r, hr⟩ := marker_blocks hmu
  obtain ⟨s, hs⟩ := marker_blocks hmv
  have hc₁ := hu.2.1.1
  have hc₂ := hv.2.1.1
  simp only [hr, hs, outstandingBodies] at hc₁ hc₂
  have hrs : r = s := by omega
  rw [hr, hs, hrs]

theorem advanceRemainder_to_first_marker {w v : LabeledWord} {xs : List ℕ}
    (hw : w.CursorInvariant) (hstart : w.parser ≠ .start) (hbody : w.EmptyBodies)
    (hp : Macro.Pending w) (hn : w.NoRootPassed)
    (hraw : w.runAtoms (xs.map fun n => (∅, n)) = some v)
    (hv : v.markerEvent = true) (hvn : v.NoRootPassed) :
    advanceRemainder.run w xs = some v := by
  apply response_eq_of_endpoint_parser advanceRemainder (fun _ _ => rfl) hraw
    (by simp [advanceRemainder, event, hv])
  intro _front _tail u _hxs hf _ht
  have hlu := zero_run_legal advanceRemainder (fun _ _ => rfl) hf
  have hlv := legal_of_zero_atoms hraw
  have hmu := Macro.first_marker_of_pending hw hstart hbody hp hf
  have hnu := hn.remainder hstart hf
  have hroot : u.rootLabel = v.rootLabel :=
    (hlu.rootLabel_eq hstart).trans (hlv.rootLabel_eq hstart).symm
  have hcount := hnu.body_length_eq hvn hmu hv hroot
  exact marker_parser_eq (hlu.cursorInvariant hw) (hlv.cursorInvariant hw) hmu hv hcount
    ((hlu.rootMarker_eq hstart).trans (hlv.rootMarker_eq hstart).symm)

#print axioms advanceRemainder_to_first_marker

end Erdos591.Positive.Game.LabeledWord
