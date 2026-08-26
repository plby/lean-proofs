import ErdosProblems.Erdos591.MarkerPrefixAcceptance

/-!
# Shared coordinate prefixes with a different root label

The upper labeling in last--first gluing is not a coarsening: it may
select later bodies not selected by the lower labeling. Before its first
selected body, however, all its body labels are empty. The cursor below
keeps the exact coordinates and structural counters, replaces the root
label, and empties the stored body labels. Its execution uses the original
`read` and response parsers; no label is changed in a submitted play.
-/

namespace Erdos591.Positive.Game.LabeledWord

def rootRelabel (C : Finset ℕ) (w : LabeledWord) : LabeledWord :=
  {w with rootLabel := C, bodyLabels := List.replicate w.bodyLabels.length ∅}

theorem rootRelabel_emptyBodies (C : Finset ℕ) (w : LabeledWord) :
    (rootRelabel C w).EmptyBodies := by
  intro D hD
  simpa [rootRelabel] using (List.mem_replicate.mp hD).2

theorem read_rootRelabel {w v : LabeledWord} {D C : Finset ℕ} {n : ℕ}
    (hw : w.parser ≠ .start) (hr : w.read D n = some v) :
    (rootRelabel C w).read ∅ n = some (rootRelabel C v) := by
  cases hs : Parser.step w.parser n with
  | none => simp [LabeledWord.read, hs] at hr
  | some p =>
      have heq : w.record D n p = v := by simpa [LabeledWord.read, hs] using hr
      subst v
      have heq' : (rootRelabel C w).record ∅ n p = rootRelabel C (w.record D n p) := by
        cases hp : w.parser with
        | start => exact (hw hp).elim
        | leaves r k => simp [rootRelabel, record, hp]
        | blocks r =>
            cases r <;> simp [rootRelabel, record, hp, List.replicate_succ']
      simpa only [LabeledWord.read, rootRelabel, hs, Option.map_some] using
        congrArg some heq'

theorem runAtoms_rootRelabel {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (C : Finset ℕ) (hw : w.parser ≠ .start) (hr : w.runAtoms xs = some v) :
    (rootRelabel C w).runAtoms ((xs.map Prod.snd).map fun n => (∅, n)) =
      some (rootRelabel C v) := by
  induction xs generalizing w with
  | nil =>
      have heq : w = v := Option.some.inj hr
      simp [heq]
  | cons a xs ih =>
      cases hread : w.read a.1 a.2 with
      | none => simp [runAtoms, hread] at hr
      | some u =>
          have ht : u.runAtoms xs = some v := by simpa [runAtoms, hread] using hr
          have hrel := read_rootRelabel (C := C) hw hread
          simpa [runAtoms, hrel] using ih (read_parser_ne_start hread) ht

@[simp] theorem rootRelabel_rootCursor (C D : Finset ℕ) (n : ℕ) :
    rootRelabel C (LabeledCode.rootCursor D n) = LabeledCode.rootCursor C n := rfl

/-- A root relabeling whose least selected body is the target marker
accepts exactly the lower word's coordinate prefix, ignoring its labels. -/
theorem rootRelabel_first_marker {D C : Finset ℕ} {n : ℕ} {v : LabeledWord}
    {xs : List (Finset ℕ × ℕ)}
    (hr : (LabeledCode.rootCursor D n).runAtoms xs = some v)
    (hC : ∀ i ∈ C, 0 < i ∧ i < n)
    (hm : v.markerEvent = true) (hi : v.bodyLabels.length + 1 ∈ C)
    (hmin : ∀ i ∈ C, v.bodyLabels.length + 1 ≤ i) :
    advanceRemainder.run (LabeledCode.rootCursor C n) (xs.map Prod.snd) =
      some (rootRelabel C v) := by
  have hread := LabeledCode.read_root C n
  have hcorrect := cursorInvariant_initial.read
    (show initial.AllowedLabel C n from ⟨hC, trivial⟩) hread
  have hstart := read_parser_ne_start hread
  have hbody : (LabeledCode.rootCursor C n).EmptyBodies := by
    simp [EmptyBodies, LabeledCode.rootCursor]
  have hp : Macro.Pending (LabeledCode.rootCursor C n) :=
    Or.inl ⟨v.bodyLabels.length + 1, hi, by simp [LabeledCode.rootCursor]⟩
  have hn : (LabeledCode.rootCursor C n).NoRootPassed := by
    intro i hiC
    exact (hC i hiC).1
  have hraw := runAtoms_rootRelabel C
    (show (LabeledCode.rootCursor D n).parser ≠ .start by simp [LabeledCode.rootCursor]) hr
  rw [rootRelabel_rootCursor] at hraw
  have hmarker : (rootRelabel C v).markerEvent = true := by
    obtain ⟨r, hv⟩ := marker_blocks hm
    simpa [markerEvent, rootRelabel, hv] using hi
  have hno : (rootRelabel C v).NoRootPassed := by
    intro i hiC
    simpa [rootRelabel] using hmin i hiC
  exact advanceRemainder_to_first_marker hcorrect hstart hbody hp hn hraw hmarker hno

#print axioms runAtoms_rootRelabel
#print axioms rootRelabel_first_marker

end Erdos591.Positive.Game.LabeledWord
