import ErdosProblems.Erdos591.MacroExtension

/-!
# A pending selected position cannot be skipped by a macro-extension

With positive new label size, an unread selected body creates selected
leaves before its end. A macro that has a pending selected position
therefore ends at a selected leaf, not at completion. This includes the
first macro from a root with a nonempty label.
-/

namespace Erdos591.Positive.Game.Macro

def Pending (w : LabeledWord) : Prop :=
  (∃ i ∈ w.rootLabel, w.bodyLabels.length < i) ∨
    (w.bodyLabels.length ∈ w.rootLabel ∧
      ∃ j ∈ w.currentLabel, w.leafIndex < j)

theorem not_pending_of_no_outstanding {w : LabeledWord}
    (hw : w.CursorInvariant)
    (hb : LabeledWord.outstandingBodies w.parser = 0)
    (hl : LabeledWord.outstandingLeaves w.parser = 0) : ¬ Pending w := by
  intro hp
  have hcounts := hw.2.1
  simp only [LabeledWord.Counters, hb, hl, Nat.add_zero] at hcounts
  rcases hp with ⟨i, hi, hlt⟩ | ⟨_, j, hj, hlt⟩
  · have hi' := (hw.2.2.1 i hi).2
    omega
  · have hj' := (hw.2.2.2 j hj).2
    omega

theorem not_pending_terminal {w : LabeledWord} (hw : w.CursorInvariant)
    (ht : w.terminal = true) : ¬ Pending w := by
  have hp : w.parser = .blocks 0 := by simpa [LabeledWord.terminal] using ht
  exact not_pending_of_no_outstanding hw (by simp [hp, LabeledWord.outstandingBodies])
    (by simp [hp, LabeledWord.outstandingLeaves])

theorem pending_read {q : ℕ} (hq : 0 < q) {w v : LabeledWord}
    (hw : w.CursorInvariant) (hp : Pending w) {D : Finset ℕ} {n : ℕ}
    (hD : w.AllowedLabel D n) (hr : w.read D n = some v)
    (hsize : D.card = labelSize q w) (hrel : v.relaxed = false) : Pending v := by
  cases hs : w.parser with
  | start =>
      exact (not_pending_of_no_outstanding hw
        (by simp [hs, LabeledWord.outstandingBodies])
        (by simp [hs, LabeledWord.outstandingLeaves]) hp).elim
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hs, Parser.step] at hr
      | succ r =>
          have heq : w.record D n (Parser.normalize r n) = v := by
            simpa [LabeledWord.read, hs, Parser.step] using hr
          subst v
          have hfuture : ∃ i ∈ w.rootLabel, w.bodyLabels.length < i := by
            rcases hp with hf | ⟨_, j, hj, hlt⟩
            · exact hf
            · have hc := hw.2.1.2
              have hj' := (hw.2.2.2 j hj).2
              simp [hs, LabeledWord.outstandingLeaves] at hc
              omega
          obtain ⟨i, hi, hlt⟩ := hfuture
          by_cases hfar : w.bodyLabels.length + 1 < i
          · left
            exact ⟨i, by simpa [LabeledWord.record, hs] using hi,
              by simpa [LabeledWord.record, hs] using hfar⟩
          · have heq : i = w.bodyLabels.length + 1 := by omega
            subst i
            have hcard : D.card = q := by
              simpa [labelSize, LabeledWord.markerEvent, hs, hi] using hsize
            obtain ⟨j, hj⟩ := Finset.card_pos.mp (hcard ▸ hq)
            right
            refine ⟨by simpa [LabeledWord.record, hs] using hi, j, ?_, ?_⟩
            · simpa [LabeledWord.currentLabel, LabeledWord.record, hs] using hj
            · simpa [LabeledWord.record, hs] using (hD.1 j hj).1
  | leaves r k =>
      have heq : w.record D n (Parser.normalize r k) = v := by
        simpa [LabeledWord.read, hs, Parser.step] using hr
      subst v
      rcases hp with ⟨i, hi, hlt⟩ | ⟨hbody, j, hj, hlt⟩
      · left
        exact ⟨i, by simpa [LabeledWord.record, hs] using hi,
          by simpa [LabeledWord.record, hs] using hlt⟩
      · have hlt' : w.leafIndex + 1 < j := by
          by_contra hn
          have heq : j = w.leafIndex + 1 := by omega
          have hevent : (w.record D n (Parser.normalize r k)).relaxed = true := by
            simp only [LabeledWord.relaxed, LabeledWord.record, hs,
              LabeledWord.currentLabel, decide_eq_true_eq]
            exact ⟨by omega, hbody, by simpa [heq, LabeledWord.currentLabel] using hj⟩
          simp [hrel] at hevent
        right
        exact ⟨by simpa [LabeledWord.record, hs] using hbody,
          j, by simpa [LabeledWord.currentLabel, LabeledWord.record, hs] using hj,
          by simpa [LabeledWord.record, hs] using hlt'⟩

/-- After the root has been fixed, a read cannot create a selected
position unless a selected body or leaf was already pending. -/
theorem pending_before_read {w v : LabeledWord} (hw : w.parser ≠ .start)
    {D : Finset ℕ} {n : ℕ} (hr : w.read D n = some v)
    (hv : Pending v ∨ v.relaxed = true) : Pending w := by
  cases hs : w.parser with
  | start => exact (hw hs).elim
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hs, Parser.step] at hr
      | succ r =>
          have heq : w.record D n (Parser.normalize r n) = v := by
            simpa [LabeledWord.read, hs, Parser.step] using hr
          subst v
          rcases hv with hp | hrel
          · rcases hp with ⟨i, hi, hlt⟩ | ⟨hi, _⟩
            · left
              refine ⟨i, by simpa [LabeledWord.record, hs] using hi, ?_⟩
              have hh : w.bodyLabels.length + 1 < i := by
                simpa [LabeledWord.record, hs] using hlt
              omega
            · left
              exact ⟨w.bodyLabels.length + 1,
                by simpa [LabeledWord.record, hs] using hi, Nat.lt_succ_self _⟩
          · simp [LabeledWord.relaxed, LabeledWord.record, hs] at hrel
  | leaves r k =>
      have heq : w.record D n (Parser.normalize r k) = v := by
        simpa [LabeledWord.read, hs, Parser.step] using hr
      subst v
      rcases hv with hp | hrel
      · rcases hp with ⟨i, hi, hlt⟩ | ⟨hi, j, hj, hlt⟩
        · left
          exact ⟨i, by simpa [LabeledWord.record, hs] using hi,
            by simpa [LabeledWord.record, hs] using hlt⟩
        · right
          refine ⟨by simpa [LabeledWord.record, hs] using hi, j,
            by simpa [LabeledWord.currentLabel, LabeledWord.record, hs] using hj, ?_⟩
          have hh : w.leafIndex + 1 < j := by simpa [LabeledWord.record, hs] using hlt
          omega
      · have hh : 0 < w.leafIndex + 1 ∧ w.bodyLabels.length ∈ w.rootLabel ∧
            w.leafIndex + 1 ∈ w.currentLabel := by
          simpa [LabeledWord.relaxed, LabeledWord.record, hs, LabeledWord.currentLabel] using hrel
        exact Or.inr ⟨hh.2.1, w.leafIndex + 1, hh.2.2, Nat.lt_succ_self _⟩

theorem Extension.terminal_of_not_pending {q : ℕ} {w v : LabeledWord}
    {xs : List (Finset ℕ × ℕ)} (h : Extension q w xs v)
    (hw : w.parser ≠ .start) (hp : ¬ Pending w) : v.terminal = true := by
  induction h with
  | stop w D n v _ hr _ hv =>
      exact hv.resolve_right (fun hrel => hp (pending_before_read hw hr (Or.inr hrel)))
  | more w D n v xs last _ hr _ _ _ ih =>
      exact ih (LabeledWord.read_parser_ne_start hr)
        (fun hpv => hp (pending_before_read hw hr (Or.inl hpv)))

theorem Extension.relaxed_of_pending {q : ℕ} (hq : 0 < q)
    {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)} (h : Extension q w xs v)
    (hw : w.CursorInvariant) (hp : Pending w) : v.relaxed = true := by
  induction h with
  | stop w D n v hl hr hs hv =>
      cases hrel : v.relaxed with
      | true => rfl
      | false =>
          have hpv := pending_read hq hw hp hl hr hs hrel
          have hvt : v.terminal = true := hv.resolve_right (by simp [hrel])
          exact (not_pending_terminal (hw.read hl hr) hvt hpv).elim
  | more w D n v xs last hl hr hs hcont _ ih =>
      have hrel : v.relaxed = false := by cases hh : v.relaxed <;> simp_all
      exact ih (hw.read hl hr) (pending_read hq hw hp hl hr hs hrel)

/-- A new positive-size root branch always reaches an unfinished
selected-leaf prefix. This is not assumed from macro termination. -/
theorem Extension.initial_relaxed {q : ℕ} (hq : 0 < q)
    {v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : Extension q LabeledWord.initial xs v) : v.relaxed = true := by
  have root_pending (D : Finset ℕ) (n : ℕ) (u : LabeledWord)
      (hl : LabeledWord.initial.AllowedLabel D n)
      (hr : LabeledWord.initial.read D n = some u)
      (hs : D.card = labelSize q LabeledWord.initial) : Pending u := by
    have hcard : D.card = q := by simpa [labelSize, LabeledWord.initial] using hs
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (hcard ▸ hq)
    have heq : u = LabeledCode.rootCursor D n :=
      Option.some.inj (hr.symm.trans (LabeledCode.read_root D n))
    left
    refine ⟨i, ?_, ?_⟩
    · simpa [heq, LabeledCode.rootCursor] using hi
    · simpa [heq, LabeledCode.rootCursor] using (hl.1 i hi).1
  cases h with
  | stop w D n v hl hr hs hv =>
      have hp := root_pending D n v hl hr hs
      have hw := LabeledWord.cursorInvariant_initial.read hl hr
      exact hv.resolve_left (fun ht => not_pending_terminal hw ht hp)
  | more w D n u xs last hl hr hs _ ht =>
      exact ht.relaxed_of_pending hq (LabeledWord.cursorInvariant_initial.read hl hr)
        (root_pending D n u hl hr hs)

theorem Extension.initial_root_card {q : ℕ} {v : LabeledWord}
    {xs : List (Finset ℕ × ℕ)} (h : Extension q LabeledWord.initial xs v) :
    v.rootLabel.card = q := by
  have root_card (D : Finset ℕ) (n : ℕ) (u : LabeledWord)
      (hr : LabeledWord.initial.read D n = some u)
      (hs : D.card = labelSize q LabeledWord.initial) : u.rootLabel.card = q := by
    have heq : u = LabeledCode.rootCursor D n :=
      Option.some.inj (hr.symm.trans (LabeledCode.read_root D n))
    simpa [heq, LabeledCode.rootCursor, labelSize, LabeledWord.initial] using hs
  cases h with
  | stop _ D n v _ hr hs _ => exact root_card D n v hr hs
  | more _ D n u xs last _ hr hs _ ht =>
      rw [ht.legal.rootLabel_eq (LabeledWord.read_parser_ne_start hr)]
      exact root_card D n u hr hs

#print axioms pending_read
#print axioms Extension.initial_relaxed
#print axioms Extension.initial_root_card
#print axioms Extension.terminal_of_not_pending

end Erdos591.Positive.Game.Macro
