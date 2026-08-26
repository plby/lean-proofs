import ErdosProblems.Erdos591.MacroPending

/-!
# Exact finite rank parameters of macro-extensions

The two parameters count selected bodies strictly after the current
body and selected leaves strictly after the current leaf. They are the
exponents in the descendant lower bound `theta ^ t * omega ^ k`.
-/

namespace Erdos591.Positive.Game.Macro

def after (D : Finset ℕ) (i : ℕ) : Finset ℕ := D.filter (i < ·)

theorem after_succ (D : Finset ℕ) (i : ℕ) :
    after D (i + 1) = (after D i).erase (i + 1) := by
  ext j
  simp only [after, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hj, hlt⟩
    exact ⟨by omega, hj, by omega⟩
  · rintro ⟨hne, hj, hlt⟩
    exact ⟨hj, by omega⟩

theorem after_card_succ_of_mem (D : Finset ℕ) (i : ℕ) (hi : i + 1 ∈ D) :
    (after D (i + 1)).card + 1 = (after D i).card := by
  rw [after_succ]
  apply Finset.card_erase_add_one
  simpa [after] using hi

theorem after_succ_of_not_mem (D : Finset ℕ) (i : ℕ) (hi : i + 1 ∉ D) :
    after D (i + 1) = after D i := by
  rw [after_succ, Finset.erase_eq_of_notMem]
  simpa [after] using hi

theorem after_zero (D : Finset ℕ) (hD : ∀ i ∈ D, 0 < i) : after D 0 = D := by
  exact Finset.filter_true_of_mem hD

def bodyRank (w : LabeledWord) : ℕ := (after w.rootLabel w.bodyLabels.length).card

def leafRank (w : LabeledWord) : ℕ :=
  if w.bodyLabels.length ∈ w.rootLabel then (after w.currentLabel w.leafIndex).card else 0

theorem bodyRank_pos_iff (w : LabeledWord) :
    0 < bodyRank w ↔ ∃ i ∈ w.rootLabel, w.bodyLabels.length < i := by
  simp [bodyRank, Finset.card_pos, after, Finset.Nonempty]

theorem leafRank_pos_iff (w : LabeledWord) :
    0 < leafRank w ↔ w.bodyLabels.length ∈ w.rootLabel ∧
      ∃ j ∈ w.currentLabel, w.leafIndex < j := by
  by_cases hsel : w.bodyLabels.length ∈ w.rootLabel <;>
    simp [leafRank, hsel, Finset.card_pos, after, Finset.Nonempty]

theorem pending_iff_ranks (w : LabeledWord) : Pending w ↔ 0 < bodyRank w ∨ 0 < leafRank w := by
  rw [bodyRank_pos_iff, leafRank_pos_iff]
  rfl

theorem terminal_ranks {w : LabeledWord} (hw : w.CursorInvariant)
    (ht : w.terminal = true) : bodyRank w = 0 ∧ leafRank w = 0 := by
  have hn := not_pending_terminal hw ht
  rw [pending_iff_ranks] at hn
  omega

theorem parser_ne_start_of_rank {w : LabeledWord} (hw : w.CursorInvariant)
    (hp : 0 < bodyRank w ∨ 0 < leafRank w) : w.parser ≠ .start := by
  intro hs
  exact not_pending_of_no_outstanding hw
    (by simp [hs, LabeledWord.outstandingBodies])
    (by simp [hs, LabeledWord.outstandingLeaves]) ((pending_iff_ranks w).2 hp)

theorem leafRank_blocks {w : LabeledWord} (hw : w.CursorInvariant) {r : ℕ}
    (hs : w.parser = .blocks r) : leafRank w = 0 := by
  by_contra hn
  obtain ⟨_, j, hj, hlt⟩ := (leafRank_pos_iff w).1 (Nat.pos_of_ne_zero hn)
  have hc := hw.2.1.2
  have hb := (hw.2.2.2 j hj).2
  simp only [hs, LabeledWord.outstandingLeaves, Nat.add_zero] at hc
  omega

/-- One non-root coordinate either consumes one selected leaf, changes
neither parameter, or enters one selected body with a new `q`-element
label. -/
inductive RankStep (q : ℕ) (w v : LabeledWord) : Prop
  | selectedLeaf (hrel : v.relaxed = true)
      (ht : bodyRank v = bodyRank w) (hk : leafRank v + 1 = leafRank w)
  | ordinary (hrel : v.relaxed = false)
      (ht : bodyRank v = bodyRank w) (hk : leafRank v = leafRank w)
  | selectedBody (hrel : v.relaxed = false)
      (ht : bodyRank v + 1 = bodyRank w) (hk : leafRank v = q) (hzero : leafRank w = 0)

theorem rankStep_read {q : ℕ} {w v : LabeledWord} (hw : w.CursorInvariant)
    (hstart : w.parser ≠ .start) {D : Finset ℕ} {n : ℕ}
    (hD : w.AllowedLabel D n) (hr : w.read D n = some v)
    (hsize : D.card = labelSize q w) : RankStep q w v := by
  cases hs : w.parser with
  | start => exact (hstart hs).elim
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hs, Parser.step] at hr
      | succ r =>
          have heq : w.record D n (Parser.normalize r n) = v := by
            simpa [LabeledWord.read, hs, Parser.step] using hr
          subst v
          have hzero := leafRank_blocks hw hs
          have hrel : (w.record D n (Parser.normalize r n)).relaxed = false := by
            simp [LabeledWord.relaxed, LabeledWord.record, hs]
          by_cases hsel : w.bodyLabels.length + 1 ∈ w.rootLabel
          · apply RankStep.selectedBody hrel _ _ hzero
            · simpa [bodyRank, LabeledWord.record, hs] using
                after_card_succ_of_mem w.rootLabel w.bodyLabels.length hsel
            · have hcard : D.card = q := by
                simpa [labelSize, LabeledWord.markerEvent, hs, hsel] using hsize
              have hafter := after_zero D (fun i hi => (hD.1 i hi).1)
              simpa [leafRank, LabeledWord.record, hs, LabeledWord.currentLabel,
                hsel, hafter] using hcard
          · apply RankStep.ordinary hrel
            · simpa [bodyRank, LabeledWord.record, hs] using
                congrArg Finset.card (after_succ_of_not_mem w.rootLabel w.bodyLabels.length hsel)
            · rw [hzero]
              simp [leafRank, LabeledWord.record, hs, hsel]
  | leaves r k =>
      have heq : w.record D n (Parser.normalize r k) = v := by
        simpa [LabeledWord.read, hs, Parser.step] using hr
      subst v
      have ht : bodyRank (w.record D n (Parser.normalize r k)) = bodyRank w := by
        simp [bodyRank, LabeledWord.record, hs]
      by_cases hbody : w.bodyLabels.length ∈ w.rootLabel
      · by_cases hleaf : w.leafIndex + 1 ∈ w.currentLabel
        · refine RankStep.selectedLeaf ?_ ht ?_
          · simpa [LabeledWord.relaxed, LabeledWord.record, hs,
              LabeledWord.currentLabel, hbody] using hleaf
          · simpa [leafRank, LabeledWord.record, hs, LabeledWord.currentLabel, hbody] using
              after_card_succ_of_mem w.currentLabel w.leafIndex hleaf
        · refine RankStep.ordinary ?_ ht ?_
          · simpa [LabeledWord.relaxed, LabeledWord.record, hs,
              LabeledWord.currentLabel, hbody] using hleaf
          · simpa [leafRank, LabeledWord.record, hs, LabeledWord.currentLabel, hbody] using
              congrArg Finset.card (after_succ_of_not_mem w.currentLabel w.leafIndex hleaf)
      · refine RankStep.ordinary ?_ ht ?_
        · simp [LabeledWord.relaxed, LabeledWord.record, hs, hbody]
        · simp [leafRank, LabeledWord.record, hs, hbody]

/-- If a selected leaf remains in the current body, a macro consumes
exactly one such leaf and leaves the number of later selected bodies
unchanged. This case does not require a positive new-label parameter. -/
theorem Extension.current_rank {q : ℕ} {w v : LabeledWord}
    {xs : List (Finset ℕ × ℕ)} (h : Extension q w xs v)
    (hw : w.CursorInvariant) (hk : 0 < leafRank w) :
    v.relaxed = true ∧ bodyRank v = bodyRank w ∧ leafRank v + 1 = leafRank w := by
  induction h with
  | stop w D n v hl hr hs hv =>
      have hvInv := hw.read hl hr
      cases rankStep_read hw (parser_ne_start_of_rank hw (Or.inr hk)) hl hr hs with
      | selectedLeaf hrel ht hk' => exact ⟨hrel, ht, hk'⟩
      | ordinary hrel ht hk' =>
          have hterm := hv.resolve_right (by simp [hrel])
          have hz := (terminal_ranks hvInv hterm).2
          omega
      | selectedBody _ _ _ hz => omega
  | more w D n v xs last hl hr hs hcont _ ih =>
      have hvInv := hw.read hl hr
      cases rankStep_read hw (parser_ne_start_of_rank hw (Or.inr hk)) hl hr hs with
      | selectedLeaf hrel _ _ => exact (hcont (Or.inr hrel)).elim
      | ordinary _ ht hk' =>
          obtain ⟨hrel, ht', hk''⟩ := ih hvInv (hk' ▸ hk)
          exact ⟨hrel, ht'.trans ht, hk''.trans hk'⟩
      | selectedBody _ _ _ hz => omega

/-- Once the current body's selected leaves are exhausted, a macro
enters exactly the next selected body and consumes its first selected
leaf. The new label has exactly `q` elements. -/
theorem Extension.future_rank {q : ℕ} (hq : 0 < q) {w v : LabeledWord}
    {xs : List (Finset ℕ × ℕ)} (h : Extension q w xs v)
    (hw : w.CursorInvariant) (hk : leafRank w = 0) (ht : 0 < bodyRank w) :
    v.relaxed = true ∧ bodyRank v + 1 = bodyRank w ∧ leafRank v + 1 = q := by
  induction h with
  | stop w D n v hl hr hs hv =>
      have hvInv := hw.read hl hr
      cases rankStep_read hw (parser_ne_start_of_rank hw (Or.inl ht)) hl hr hs with
      | selectedLeaf _ _ hk' => omega
      | ordinary hrel ht' _ =>
          have hterm := hv.resolve_right (by simp [hrel])
          have hz := (terminal_ranks hvInv hterm).1
          omega
      | selectedBody hrel _ hk' _ =>
          have hterm := hv.resolve_right (by simp [hrel])
          have hz := (terminal_ranks hvInv hterm).2
          omega
  | more w D n v xs last hl hr hs hcont htail ih =>
      have hvInv := hw.read hl hr
      cases rankStep_read hw (parser_ne_start_of_rank hw (Or.inl ht)) hl hr hs with
      | selectedLeaf _ _ hk' => omega
      | ordinary _ ht' hk' =>
          obtain ⟨hrel, ht'', hk''⟩ := ih hvInv (hk'.trans hk) (ht' ▸ ht)
          exact ⟨hrel, ht''.trans ht', hk''⟩
      | selectedBody _ ht' hk' _ =>
          obtain ⟨hrel, ht'', hk''⟩ := htail.current_rank hvInv (hk' ▸ hq)
          exact ⟨hrel, by omega, hk''.trans hk'⟩

theorem rootCursor_ranks {D : Finset ℕ} {n : ℕ}
    (hD : ∀ i ∈ D, 0 < i) :
    bodyRank (LabeledCode.rootCursor D n) = D.card ∧
      leafRank (LabeledCode.rootCursor D n) = 0 := by
  constructor
  · change (after D 0).card = D.card
    rw [after_zero D hD]
  · simp [leafRank, LabeledCode.rootCursor, LabeledWord.currentLabel, after]

/-- Both finite exponents after the first macro are exactly one less
than the prescribed positive label size. -/
theorem Extension.initial_ranks {q : ℕ} (hq : 0 < q)
    {v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : Extension q LabeledWord.initial xs v) :
    v.relaxed = true ∧ bodyRank v + 1 = q ∧ leafRank v + 1 = q := by
  have root_ranks (D : Finset ℕ) (n : ℕ) (u : LabeledWord)
      (hl : LabeledWord.initial.AllowedLabel D n)
      (hr : LabeledWord.initial.read D n = some u)
      (hs : D.card = labelSize q LabeledWord.initial) :
      bodyRank u = q ∧ leafRank u = 0 := by
    have heq : u = LabeledCode.rootCursor D n :=
      Option.some.inj (hr.symm.trans (LabeledCode.read_root D n))
    have hc : D.card = q := by simpa [labelSize, LabeledWord.initial] using hs
    simpa [heq, hc] using rootCursor_ranks (fun i hi => (hl.1 i hi).1)
  cases h with
  | stop _ D n v hl hr hs hv =>
      have ⟨ht, _⟩ := root_ranks D n v hl hr hs
      have hrel : v.relaxed = false := by
        have heq : v = LabeledCode.rootCursor D n :=
          Option.some.inj (hr.symm.trans (LabeledCode.read_root D n))
        simp [heq, LabeledCode.rootCursor, LabeledWord.relaxed]
      have hterm := hv.resolve_right (by simp [hrel])
      have hz := (terminal_ranks (LabeledWord.cursorInvariant_initial.read hl hr) hterm).1
      omega
  | more _ D n u xs last hl hr hs _ htail =>
      obtain ⟨ht, hk⟩ := root_ranks D n u hl hr hs
      simpa [ht] using htail.future_rank hq
        (LabeledWord.cursorInvariant_initial.read hl hr) hk (ht ▸ hq)

#print axioms rankStep_read
#print axioms Extension.current_rank
#print axioms Extension.future_rank
#print axioms Extension.initial_ranks

end Erdos591.Positive.Game.Macro
