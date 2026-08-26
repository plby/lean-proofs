import ErdosProblems.Erdos118.Reused591.NextLeafAcceptance
import ErdosProblems.Erdos118.Reused591.BeforeBody

namespace Erdos118.Reused591

/-!
# Exact stopping at the next selected body with past labels retained

Once all selected leaves of the current body have been read, empty new
labels create no selected leaf. The next first-event response therefore
stops at the least still-unread root-label index. Previously stored body
labels are left untouched throughout the argument.
-/

namespace Erdos591.Positive.Game.LabeledWord

def NoLeafPending (w : LabeledWord) : Prop := ∀ k ∈ w.currentLabel, k ≤ w.leafIndex

theorem NoLeafPending.read {w v : LabeledWord} (h : w.NoLeafPending)
    (hstart : w.parser ≠ .start) {n : ℕ} (hr : w.read ∅ n = some v) :
    v.NoLeafPending ∧ v.relaxed = false := by
  cases hp : w.parser with
  | start => exact (hstart hp).elim
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hp, Parser.step] at hr
      | succ r =>
          have he : w.record ∅ n (Parser.normalize r n) = v := by
            simpa [LabeledWord.read, hp, Parser.step] using hr
          subst v
          simp [NoLeafPending, currentLabel, relaxed, record, hp]
  | leaves r k =>
      have he : w.record ∅ n (Parser.normalize r k) = v := by
        simpa [LabeledWord.read, hp, Parser.step] using hr
      subst v
      constructor
      · intro j hj
        have hj' : j ∈ w.currentLabel := by simpa [currentLabel, record, hp] using hj
        simpa [record, hp] using (h j hj').trans (Nat.le_succ _)
      · have hn : w.leafIndex + 1 ∉ w.currentLabel := by
          intro hj
          have he := h _ hj
          omega
        simp [relaxed, record, hp, currentLabel] at hn ⊢
        exact fun _ => hn

theorem NoLeafPending.zero_run {w v : LabeledWord} {xs : List ℕ}
    (h : w.NoLeafPending) (hstart : w.parser ≠ .start) (hrel : w.relaxed = false)
    (hr : w.runAtoms (xs.map fun n => (∅, n)) = some v) :
    v.NoLeafPending ∧ v.relaxed = false := by
  induction xs generalizing w with
  | nil =>
      have he : w = v := Option.some.inj hr
      exact he ▸ ⟨h, hrel⟩
  | cons n xs ih =>
      cases hr₁ : w.read ∅ n with
      | none => simp [runAtoms, hr₁] at hr
      | some u =>
          have ht : u.runAtoms (xs.map fun n => (∅, n)) = some v := by
            simpa [runAtoms, hr₁] using hr
          have hu := h.read hstart hr₁
          exact ih hu.1 (read_parser_ne_start hr₁) hu.2 ht

theorem advanceRemainder_to_next_marker {w v : LabeledWord} {xs : List ℕ} {i base : ℕ}
    (hw : w.CursorInvariant) (hstart : w.parser ≠ .start)
    (hn : w.NoLeafPending) (hrel : w.relaxed = false)
    (hs : BeforeBody i w) (hbase : base ≤ w.bodyLabels.length)
    (hnext : ∀ k ∈ w.rootLabel, base < k → i ≤ k)
    (hraw : w.runAtoms (xs.map fun n => (∅, n)) = some v)
    (hv : v.markerEvent = true) (hindex : v.bodyLabels.length + 1 = i) :
    advanceRemainder.run w xs = some v := by
  have hlv := legal_of_zero_atoms hraw
  apply response_eq_of_endpoint_parser advanceRemainder (fun _ _ => rfl) hraw
    (by simp [advanceRemainder, event, hv])
  intro _front _tail u _hxs hf _ht
  have hlu := zero_run_legal advanceRemainder (fun _ _ => rfl) hf
  have hbefore := hs.remainder hstart hf
  have hcu := hlu.cursorInvariant hw
  have hnotterm := hbefore.not_terminal hcu
  have hnotrel := (hn.zero_run hstart hrel hlu.run).2
  have hevent := advanceRemainder.run_stopped hf
  have hmu : u.markerEvent = true := by
    simpa [advanceRemainder, event, hnotterm, hnotrel] using hevent
  have hmem : u.bodyLabels.length + 1 ∈ w.rootLabel :=
    hlu.rootLabel_eq hstart ▸ marker_body_mem hmu
  have hlen := (hlu.bodyLabels_prefix hstart).length_le
  have hlarge := hnext _ hmem (by omega)
  have hcount : u.bodyLabels.length = v.bodyLabels.length := by
    have hsmall := hbefore.2
    omega
  exact marker_parser_eq hcu (hlv.cursorInvariant hw) hmu hv hcount
    ((hlu.rootMarker_eq hstart).trans (hlv.rootMarker_eq hstart).symm)

#print axioms advanceRemainder_to_next_marker

end Erdos591.Positive.Game.LabeledWord

end Erdos118.Reused591
